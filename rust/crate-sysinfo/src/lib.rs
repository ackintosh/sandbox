#[cfg(test)]
mod tests {
    use sysinfo::{DiskExt, NetworkExt, NetworksExt, System, SystemExt};

    #[test]
    fn it_works() {
        let sysinfo = System::new_all();

        // 以下、lighthouseでとっているメトリクス

        // Memory
        // ※psutilでは単位がbyte
        println!("total memory:     {} KB", sysinfo.total_memory());
        // available_memory を計算しているコード(macOS)
        // https://github.com/GuillaumeGomez/sysinfo/blob/master/src/apple/system.rs#L245-L261
        println!("available memory: {} KB", sysinfo.available_memory());
        println!("used memory: {} KB", sysinfo.used_memory());
        println!("free memory: {} KB", sysinfo.free_memory());
        // println!("cached memory: {} KB", sysinfo.free_memory());
        // println!("buffers memory: {} KB", sysinfo.free_memory());
        // 参考
        // https://github.com/rust-psutil/rust-psutil/blob/master/src/memory/sys/macos/virtual_memory.rs#L52
        println!(
            "percent: {} %",
            (((sysinfo.total_memory() as f64 - sysinfo.available_memory() as f64)
                / sysinfo.total_memory() as f64)
                * 100.0) as f32
        );

        // Loadavg
        let loadavg = sysinfo.load_average();
        println!("loadavg 1: {}", loadavg.one);
        println!("loadavg 5: {}", loadavg.five);
        println!("loadavg 15: {}", loadavg.fifteen);

        // CPU
        println!("cpu cores: {:?}", sysinfo.physical_core_count());
        // 違うかも?
        println!("cpu threads: {}", sysinfo.processors().len());
        // println!("system seconds total: {:?}", sysinfo.processors().len());
        // println!("cpu time total: {:?}", sysinfo.processors().len());
        // println!("user seconds total: {:?}", sysinfo.processors().len());
        // println!("iowait seconds total: {:?}", sysinfo.processors().len());
        // println!("idle seconds total: {:?}", sysinfo.processors().len());

        // Disk
        println!(
            "disk bytes total: {}",
            sysinfo.disks().iter().map(|d| d.total_space()).sum::<u64>()
        );
        println!(
            "disk bytes free: {}",
            sysinfo
                .disks()
                .iter()
                .map(|d| d.available_space())
                .sum::<u64>()
        );
        // println!("disk reads total: {:?}", sysinfo.disks().iter().map(|d| d.available_space()).sum::<u64>());
        // println!("disk writes total: {:?}", sysinfo.disks().iter().map(|d| d.available_space()).sum::<u64>());

        // Network
        println!(
            "network bytes total received: {}",
            sysinfo
                .networks()
                .iter()
                .map(|(_, n)| n.total_received())
                .sum::<u64>()
        );
        println!(
            "network bytes total transmit: {}",
            sysinfo
                .networks()
                .iter()
                .map(|(_, n)| n.total_transmitted())
                .sum::<u64>()
        );

        // Misc
        // lighthouseの実装
        //   -> 名前が boot_time だが、正確には uptime のはず
        // https://github.com/sigp/lighthouse/blob/375e2b49b3696115ac0b6bb6defef365a46374ec/common/eth2/src/lighthouse.rs#L190-L194
        println!("misc boot ts seconds: {}", sysinfo.uptime());
        println!("misc os: {:?}", sysinfo.long_os_version());
    }
}
