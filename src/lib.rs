//! This is a [Base64](https://en.wikipedia.org/wiki/Base64) encoder
//! and decoder.
//!
//! Use [`encode`] to encode slices of bytes and [`decode`] to decode
//! Base64 strings back to bytes.

#![warn(rust_2018_idioms)]
#![warn(clippy::pedantic)]

use core::fmt;
use std::error::Error;

use itertools::{enumerate, Itertools};
use phf::phf_map;

const BASE64_LOOKUP_TABLE: [char; 64] = [
    'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S',
    'T', 'U', 'V', 'W', 'X', 'Y', 'Z', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l',
    'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', '0', '1', '2', '3', '4',
    '5', '6', '7', '8', '9', '+', '/',
];
const PADDING: char = '=';

static BASE64_REVERSE_LOOKUP_TABLE: phf::Map<char, u8> = phf_map! {
    'A' => 0,
    'B' => 1,
    'C' => 2,
    'D' => 3,
    'E' => 4,
    'F' => 5,
    'G' => 6,
    'H' => 7,
    'I' => 8,
    'J' => 9,
    'K' => 10,
    'L' => 11,
    'M' => 12,
    'N' => 13,
    'O' => 14,
    'P' => 15,
    'Q' => 16,
    'R' => 17,
    'S' => 18,
    'T' => 19,
    'U' => 20,
    'V' => 21,
    'W' => 22,
    'X' => 23,
    'Y' => 24,
    'Z' => 25,
    'a' => 26,
    'b' => 27,
    'c' => 28,
    'd' => 29,
    'e' => 30,
    'f' => 31,
    'g' => 32,
    'h' => 33,
    'i' => 34,
    'j' => 35,
    'k' => 36,
    'l' => 37,
    'm' => 38,
    'n' => 39,
    'o' => 40,
    'p' => 41,
    'q' => 42,
    'r' => 43,
    's' => 44,
    't' => 45,
    'u' => 46,
    'v' => 47,
    'w' => 48,
    'x' => 49,
    'y' => 50,
    'z' => 51,
    '0' => 52,
    '1' => 53,
    '2' => 54,
    '3' => 55,
    '4' => 56,
    '5' => 57,
    '6' => 58,
    '7' => 59,
    '8' => 60,
    '9' => 61,
    '+' => 62,
    '/' => 63,
};

#[must_use]
pub fn encode(input: &[u8]) -> String {
    const CHUNK_SIZE: usize = 3;
    let mut base_64_str = String::with_capacity((input.len() * 8) / 6 + 1);
    for chunk in input.chunks(CHUNK_SIZE) {
        if chunk.len() < CHUNK_SIZE {
            // we are at the end of the slice and we got an incomplete
            // chunk, insert padding

            if chunk.len() == 1 {
                let piece_a = chunk[0] >> 2;
                let piece_b = (chunk[0] & 0x3) << 4;
                base_64_str.push(BASE64_LOOKUP_TABLE[piece_a as usize]);
                base_64_str.push(BASE64_LOOKUP_TABLE[piece_b as usize]);
                base_64_str.push(PADDING);
                base_64_str.push(PADDING);
            } else if chunk.len() == 2 {
                let piece_a = chunk[0] >> 2;
                let piece_b = ((chunk[0] & 0x3) << 4) | (chunk[1] >> 4);
                let piece_c = (chunk[1] & 0xf) << 2;
                base_64_str.push(BASE64_LOOKUP_TABLE[piece_a as usize]);
                base_64_str.push(BASE64_LOOKUP_TABLE[piece_b as usize]);
                base_64_str.push(BASE64_LOOKUP_TABLE[piece_c as usize]);
                base_64_str.push(PADDING);
            } else {
                unreachable!();
            }
        } else {
            // normal processing of exact sized chunks

            let piece_a = chunk[0] >> 2;
            let piece_b = ((chunk[0] & 0x3) << 4) | (chunk[1] >> 4);
            let piece_c = ((chunk[1] & 0xf) << 2) | (chunk[2] >> 6);
            let piece_d = chunk[2] & 0x3F;

            base_64_str.push(BASE64_LOOKUP_TABLE[piece_a as usize]);
            base_64_str.push(BASE64_LOOKUP_TABLE[piece_b as usize]);
            base_64_str.push(BASE64_LOOKUP_TABLE[piece_c as usize]);
            base_64_str.push(BASE64_LOOKUP_TABLE[piece_d as usize]);
        }
    }

    base_64_str
}

#[derive(Debug, Eq, PartialEq)]
pub enum DecodeError {
    InvalidCharacter(char),
    InvalidChunk,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCharacter(ch) => write!(f, "invalid character \"{ch}\""),
            Self::InvalidChunk => write!(f, "invalid chunk"),
        }
    }
}

impl Error for DecodeError {}

pub fn decode(input: &str) -> Result<Vec<u8>, DecodeError> {
    const CHUNK_SIZE: usize = 4;
    let mut result = Vec::new();
    let number_of_chunks = input.chars().count() / CHUNK_SIZE;
    for (chunk_index, mut chunk) in enumerate(&input.chars().chunks(CHUNK_SIZE)) {
        let ch1: char = chunk
            .next()
            .expect("a chunk must at least contain one character");
        let ch2: Option<char> = chunk.next();
        let ch3: Option<char> = chunk.next();
        let ch4: Option<char> = chunk.next();
        if ch2.is_none() && ch3.is_none() && ch4.is_none() {
            return Err(DecodeError::InvalidChunk);
        }

        let mut binary_chunks: [Option<u8>; 3] = [None; 3];
        if let Some(value) = BASE64_REVERSE_LOOKUP_TABLE.get(&ch1) {
            binary_chunks[0] = Some(value << 2);
        } else {
            // error
            return Err(DecodeError::InvalidCharacter(ch1));
        }

        if let Some(value2) =
            BASE64_REVERSE_LOOKUP_TABLE.get(&ch2.expect("must contain a character"))
        {
            binary_chunks[0] = binary_chunks[0].map(|x| x | (value2 >> 4));
            binary_chunks[1] = Some(value2 << 4);
        } else {
            return Err(DecodeError::InvalidCharacter(ch2.unwrap()));
        }

        if let Some(value3) =
            BASE64_REVERSE_LOOKUP_TABLE.get(&ch3.expect("must contain a character"))
        {
            binary_chunks[1] = binary_chunks[1].map(|x| x | (value3 >> 2));
            binary_chunks[2] = Some(value3 << 6);
        } else if ch3 == Some(PADDING) && chunk_index + 1 == number_of_chunks {
            // PADDING is only allowed in the last chunk
            binary_chunks[1] = None;
        } else {
            return Err(DecodeError::InvalidCharacter(ch3.unwrap()));
        }

        if let Some(value4) =
            BASE64_REVERSE_LOOKUP_TABLE.get(&ch4.expect("must contain a character"))
        {
            binary_chunks[2] = binary_chunks[2].map(|x| x | value4);
        } else if ch4 == Some(PADDING) && chunk_index + 1 == number_of_chunks {
            // PADDING is only allowed in the last chunk
            binary_chunks[2] = None;
        } else {
            return Err(DecodeError::InvalidCharacter(ch4.unwrap()));
        }

        for binary_chunk in binary_chunks.into_iter().flatten() {
            result.push(binary_chunk);
        }
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_encode_empty() {
        let result = super::encode(b"");
        assert_eq!(result, "");
    }

    #[test]
    fn test_encode_zero_byte() {
        let result = super::encode(b"\x00");
        assert_eq!(result, "AA==");
    }

    #[test]
    fn test_encode_only_complate_chunks() {
        let result = super::encode(b"fsfsdfd43");
        assert_eq!(result, "ZnNmc2RmZDQz");
    }

    #[test]
    fn test_encode_incomplete_chunksize_one() {
        let result = super::encode(b"fsfsdfd43a");
        assert_eq!(result, "ZnNmc2RmZDQzYQ==");
    }

    #[test]
    fn test_encode_incomplete_chunksize_two() {
        let result = super::encode(b"fsfsdfd43ab");
        assert_eq!(result, "ZnNmc2RmZDQzYWI=");
    }

    #[test]
    fn test_decode_empty() {
        let result = super::decode("");
        assert_eq!(result, Ok(vec![]));
    }

    #[test]
    fn test_decode_zero_byte() {
        let result = super::decode("AA==");
        assert_eq!(result, Ok([0].to_vec()));
    }

    #[test]
    fn test_decode_only_complate_chunks() {
        let result = super::decode("ZnNmc2RmZDQz");
        assert_eq!(result, Ok(b"fsfsdfd43".to_vec()));
    }

    #[test]
    fn test_decode_fails_when_invalid_character() {
        let result = super::decode("@@@@");
        assert_eq!(result, Err(super::DecodeError::InvalidCharacter('@')));
    }

    #[test]
    fn test_decode_incomplete_chunksize_one() {
        let result = super::decode("ZnNmc2RmZDQzYQ==");
        assert_eq!(result, Ok(b"fsfsdfd43a".to_vec()));
    }

    #[test]
    fn test_decode_incomplete_chunksize_two() {
        let result = super::decode("ZnNmc2RmZDQzYWI=");
        assert_eq!(result, Ok(b"fsfsdfd43ab".to_vec()));
    }

    #[test]
    fn test_decode_invalid_padding() {
        let result = super::decode("=");
        assert_eq!(result, Err(super::DecodeError::InvalidChunk));

        let result = super::decode("====");
        assert_eq!(result, Err(super::DecodeError::InvalidCharacter('=')));
    }

    #[test]
    fn test_decode_invalid_leading_padding() {
        let result = super::decode("AA==BBBB");
        assert_eq!(result, Err(super::DecodeError::InvalidCharacter('=')));
    }
}
