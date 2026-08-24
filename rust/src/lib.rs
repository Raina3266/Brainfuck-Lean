#[cfg(not(target_pointer_width = "64"))]
compile_error!("this crate only supports 64-bit targets (the verification assumes it)");

pub mod analysis;
#[cfg(feature = "fuzzing")]
pub mod differential;
#[cfg(feature = "fuzzing")]
pub mod generate;
pub mod interpreter;
#[cfg(feature = "fuzzing")]
pub mod oracle;
