mod sha256;
//mod table16;

//pub use sha256::*;
pub use sha256::*;
//pub use table16::*;
/// The size of a SHA-256 block, in 32-bit words.
pub const BLOCK_SIZE: usize = 16;
/// The size of a SHA-256 digest, in 32-bit words.
pub(crate) const DIGEST_SIZE: usize = 8;
