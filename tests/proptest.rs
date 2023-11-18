use proptest::{arbitrary::any, proptest};

use edu_base64::{decode, encode};

proptest! {
    #[test]
    fn encode_decode_test(bytes in any::<Vec<u8>>()) {
        assert_eq!(decode(&encode(&bytes)), Ok(bytes));
    }
}
