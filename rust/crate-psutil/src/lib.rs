#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        // Memory
        let vm = psutil::memory::virtual_memory().unwrap();
        println!("total memory:     {} KB", vm.total() / 1024);
        println!("available memory: {} KB", vm.available() / 1024);
        println!("used memory: {} KB", vm.used() / 1024);
        println!("free memory: {} KB", vm.free() / 1024);
        println!("percent: {}", vm.percent());
    }
}
