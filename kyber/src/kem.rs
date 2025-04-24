use crate::rng::randombytes;
use rand_core::{RngCore, CryptoRng};
use byteorder::{ByteOrder, NetworkEndian, WriteBytesExt};

use crate::{
  params::*,
  indcpa::*,
  symmetric::*,
  verify::*
};
extern crate alloc;
use alloc::{
  string::String,
  format,
  vec::Vec,
  vec,
  string::ToString
};

// Name:        crypto_kem_keypair
//
// Description: Generates public and private key
//              for CCA-secure Kyber key encapsulation mechanism
//
// Arguments:   - [u8] pk: output public key (an already allocated array of CRYPTO_PUBLICKEYBYTES bytes)
//              - [u8] sk: output private key (an already allocated array of CRYPTO_SECRETKEYBYTES bytes)
pub fn crypto_kem_keypair<R>(
  pk: &mut[u8], sk: &mut[u8], _rng: &mut R, _seed: Option<(&[u8], &[u8])> 
)
  where R: RngCore + CryptoRng
{ 
  const PK_START: usize = KYBER_SECRETKEYBYTES - (2 * KYBER_SYMBYTES);
  const SK_START: usize = KYBER_SECRETKEYBYTES-KYBER_SYMBYTES;
  const END: usize = KYBER_INDCPA_PUBLICKEYBYTES + KYBER_INDCPA_SECRETKEYBYTES;
  
  indcpa_keypair(pk, sk, _seed, _rng);

  sk[KYBER_INDCPA_SECRETKEYBYTES..END]
    .copy_from_slice(&pk[..KYBER_INDCPA_PUBLICKEYBYTES]);
  hash_h(&mut sk[PK_START..], pk, KYBER_PUBLICKEYBYTES);
  
  if let Some(s) = _seed {
    sk[SK_START..].copy_from_slice(&s.1)
  } else {
    randombytes(&mut sk[SK_START..],KYBER_SYMBYTES, _rng);
  }
}

// Name:        crypto_kem_enc
//
// Description: Generates cipher text and shared
//              secret for given public key
//
// Arguments:   - [u8] ct:       output cipher text (an already allocated array of CRYPTO_CIPHERTEXTBYTES bytes)
//              - [u8] ss:       output shared secret (an already allocated array of CRYPTO_BYTES bytes)
//              - const [u8] pk: input public key (an already allocated array of CRYPTO_PUBLICKEYBYTES bytes)
pub fn crypto_kem_enc<R>(
  ct: &mut[u8], ss: &mut[u8], pk: &[u8], _rng: &mut R,_seed: Option<&[u8]>
)
  where R: RngCore + CryptoRng
{
  let mut kr = [0u8; 2*KYBER_SYMBYTES];
  let mut buf = [0u8; 2*KYBER_SYMBYTES];
  let mut randbuf = [0u8; 2*KYBER_SYMBYTES];

  // Deterministic randbuf for KAT's
  if let Some(s) = _seed {
    randbuf[..KYBER_SYMBYTES].copy_from_slice(&s);
  } else {
    randombytes(&mut randbuf, KYBER_SYMBYTES, _rng);
  }

  // Don't release system RNG output 
  hash_h(&mut buf, &randbuf, KYBER_SYMBYTES);

  // Multitarget countermeasure for coins + contributory KEM
  hash_h(&mut buf[KYBER_SYMBYTES..], pk, KYBER_PUBLICKEYBYTES);
  hash_g(&mut kr, &buf, 2*KYBER_SYMBYTES);

  // coins are in kr[KYBER_SYMBYTES..]
  indcpa_enc(ct, &buf, pk, &kr[KYBER_SYMBYTES..]);

  // overwrite coins in kr with H(c) 
  hash_h(&mut kr[KYBER_SYMBYTES..], ct, KYBER_CIPHERTEXTBYTES);

  // hash concatenation of pre-k and H(c) to k
  kdf(ss, &kr, 2*KYBER_SYMBYTES);
}

#[derive(Debug, Clone)]
pub enum Error {
    Encrypt(String),
    Decrypt(String),
}
const KYBER_BLOCK_SIZE: usize = 32;
const LENGTH_FIELD: usize = 8;

pub fn ct_len(plaintext_len: usize) -> usize {
  core::cmp::max(
      KYBER_CIPHERTEXTBYTES,
      div_ceil(plaintext_len as f32, KYBER_BLOCK_SIZE as f32) * KYBER_CIPHERTEXTBYTES,
  ) + LENGTH_FIELD
}
fn div_ceil(a: f32, b: f32) -> usize {
  ((a + b - 1.0) / b) as _
}
pub fn encrypt<T: AsRef<[u8]>, R: AsRef<[u8]>, V: AsRef<[u8]>>(
  public_key: T,
  plaintext: R,
  nonce: V,
) -> Result<Vec<u8>, Error> {
  let full_ciphertext_len = ct_len(plaintext.as_ref().len());
  let mut out = vec![0u8; full_ciphertext_len];
  encrypt_into(public_key, plaintext, nonce, out.as_mut_slice())?;
  Ok(out)
}

pub fn encrypt_into<T: AsRef<[u8]>, R: AsRef<[u8]>, V: AsRef<[u8]>, O: AsMut<[u8]>>(
  public_key: T,
  plaintext: R,
  nonce: V,
  mut ret: O,
) -> Result<(), Error> {
  let public_key = public_key.as_ref();
  let nonce = nonce.as_ref();
  let plaintext = plaintext.as_ref();
  let plaintext_length = plaintext.len();
  let ret = ret.as_mut();

  if nonce.len() != 32 {
      return Err(Error::Encrypt(format!(
          "Nonce must be 32 bytes, got {}",
          nonce.len()
      )));
  }

  if ret.len() < ct_len(plaintext.len()) {
      return Err(Error::Encrypt(format!(
          "Bad output buffer len {}",
          ret.len()
      )));
  }

  if plaintext_length != 0 {
      let chunks = plaintext.chunks(32);

      for (chunk, output) in chunks.zip(ret.chunks_mut(KYBER_CIPHERTEXTBYTES)) {
          if chunk.len() < 32 {
              // fit the buffer to KYBER_BLOCK_SIZE
              let mut buf = [0u8; 32];
              let slice = &mut buf[..chunk.len()];
              slice.copy_from_slice(chunk);
              indcpa_enc(output, &buf, public_key, nonce);
          } else {
              indcpa_enc(output, chunk, public_key, nonce);
          }
      }
  } else {
      // fill with zeroes
      let zeroes = [0u8; 32];
      indcpa_enc(ret, &zeroes, public_key, nonce);
  }

  // append the plaintext len
  let length_pos = ret.len() - 8;
  (&mut ret[length_pos..])
      .write_u64::<NetworkEndian>(plaintext_length as u64)
      .unwrap();

  Ok(())
}

pub fn decrypt<T: AsRef<[u8]>, R: AsRef<[u8]>>(
  secret_key: T,
  ciphertext: R,
) -> Result<Vec<u8>, Error> {
  let ciphertext = ciphertext.as_ref();
  let secret_key = secret_key.as_ref();
  // calculate the length of each block
  const CIPHERTEXT_BLOCK_LEN: usize = KYBER_CIPHERTEXTBYTES;

  if ciphertext.len() < CIPHERTEXT_BLOCK_LEN {
      return Err(Error::Decrypt("The input ciphertext is too short".to_string()));
  }

  let plaintext_length = plaintext_len(ciphertext)
      .ok_or_else(|| Error::Decrypt("Invalid ciphertext input length".to_string()))?;
  let split_pt = ciphertext.len().saturating_sub(8);
  let (concatenated_ciphertexts, _) = ciphertext.split_at(split_pt);
  // pt len < 32: size must be 32
  // pt len = 32: size must be 32
  // pt len > 32: size must be div.ceil(pt.len()/32)*32
  let buffer_len = div_ceil(plaintext_length as f32, KYBER_BLOCK_SIZE as f32) * KYBER_BLOCK_SIZE;
  let mut ret = vec![0u8; buffer_len];
  // split the concatenated ciphertexts
  for (chunk, output) in concatenated_ciphertexts
      .chunks(CIPHERTEXT_BLOCK_LEN)
      .zip(ret.chunks_mut(KYBER_BLOCK_SIZE))
  {
      indcpa_dec(output, chunk, secret_key);
  }

  // finally, truncate the vec, as the final block is 32 in length, and may be more
  // than what the plaintext requires
  ret.truncate(plaintext_length);

  Ok(ret)
}
pub fn plaintext_len(ciphertext: &[u8]) -> Option<usize> {
  // The final 8 bytes are for the original length of the plaintext
  let split_pt = ciphertext.len().saturating_sub(8);
  if split_pt > ciphertext.len() || split_pt == 0 {
      return None;
  }

  let (_, field_length_be) = ciphertext.split_at(split_pt);
  let plaintext_length = byteorder::NetworkEndian::read_u64(field_length_be) as usize;
  Some(plaintext_length)
}

// Name:        crypto_kem_dec
//
// Description: Generates shared secret for given
//              cipher text and private key
//
// Arguments:   - [u8] ss:       output shared secret (an already allocated array of CRYPTO_BYTES bytes)
//              - const [u8] ct: input cipher text (an already allocated array of CRYPTO_CIPHERTEXTBYTES bytes)
//              - const [u8] sk: input private key (an already allocated array of CRYPTO_SECRETKEYBYTES bytes)
//
// On failure, ss will contain a pseudo-random value.
pub fn crypto_kem_dec(
  ss: &mut[u8], ct: &[u8], sk: &[u8]
) 
-> ()
{
  let mut buf = [0u8; 2*KYBER_SYMBYTES];
  let mut kr = [0u8; 2*KYBER_SYMBYTES];
  let mut cmp = [0u8; KYBER_CIPHERTEXTBYTES];
  let mut pk = [0u8; KYBER_INDCPA_PUBLICKEYBYTES];

  pk.copy_from_slice(
    &sk[KYBER_INDCPA_SECRETKEYBYTES..][..KYBER_INDCPA_PUBLICKEYBYTES]);
  
  indcpa_dec(&mut buf, ct, sk);

  // Multitarget countermeasure for coins + contributory KEM
  const START: usize = KYBER_SECRETKEYBYTES-2*KYBER_SYMBYTES;
  const END: usize = KYBER_SECRETKEYBYTES-KYBER_SYMBYTES; 
  buf[KYBER_SYMBYTES..].copy_from_slice(&sk[START..END]);
  hash_g(&mut kr, &buf, 2*KYBER_SYMBYTES);
  
  // coins are in kr[KYBER_SYMBYTES..] 
  indcpa_enc(&mut cmp, &buf, &pk, &kr[KYBER_SYMBYTES..]);
  let fail = verify(ct, &cmp, KYBER_CIPHERTEXTBYTES);
  // overwrite coins in kr with H(c)
  hash_h(&mut kr[KYBER_SYMBYTES..], ct, KYBER_CIPHERTEXTBYTES);
  // Overwrite pre-k with z on re-encryption failure 
  cmov(&mut kr, &sk[END..], KYBER_SYMBYTES, fail);
  // hash concatenation of pre-k and H(c) to k 
  kdf(ss, &kr, 2*KYBER_SYMBYTES);
}

