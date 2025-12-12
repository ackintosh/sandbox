#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(addr) = multiaddr::Multiaddr::try_from(data.to_vec()) {
        for p in addr.iter() {
            let _ = p.tag();
        }
    }
});
