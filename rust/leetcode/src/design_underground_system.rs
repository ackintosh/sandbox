// https://leetcode.com/problems/design-underground-system/

use std::collections::hash_map::Entry;
use std::collections::HashMap;

struct UndergroundSystem {
    check_ins: HashMap<i32, (String, i32)>,
    traveling_times: HashMap<String, Vec<i32>>,
}

/**
 * `&self` means the method takes an immutable reference
 * If you need a mutable reference, change it to `&mut self` instead.
 */
impl UndergroundSystem {
    fn new() -> Self {
        UndergroundSystem {
            check_ins: HashMap::new(),
            traveling_times: HashMap::new(),
        }
    }

    fn check_in(&mut self, id: i32, station_name: String, t: i32) {
        match self.check_ins.entry(id) {
            Entry::Occupied(entry) => {
                panic!(
                    "Failed to check_in {station_name}. {id} has already checked in {:?}.",
                    entry.get()
                );
            }
            Entry::Vacant(entry) => {
                entry.insert((station_name, t));
            }
        }
    }

    fn check_out(&mut self, id: i32, station_name: String, t: i32) {
        match self.check_ins.entry(id) {
            Entry::Occupied(entry) => {
                let segment = format!("{}_{}", entry.get().0, station_name);
                let elapsed_time = t - entry.get().1;

                let traveling_times = self.traveling_times.entry(segment).or_insert(vec![]);
                traveling_times.push(elapsed_time);
                entry.remove_entry();
            }
            Entry::Vacant(_) => {
                panic!(
                    "Failed to check_out {} {} due to no check_in logs.",
                    id, station_name
                );
            }
        }
    }

    fn get_average_time(&self, start_station: String, end_station: String) -> f64 {
        let segment = format!("{}_{}", start_station, end_station);
        self.traveling_times
            .get(&segment)
            .map(|t| {
                let len = t.len();
                t.iter().sum::<i32>() as f64 / len as f64
            })
            .unwrap_or(0.0)
    }
}

/**
 * Your UndergroundSystem object will be instantiated and called as such:
 * let obj = UndergroundSystem::new();
 * obj.check_in(id, stationName, t);
 * obj.check_out(id, stationName, t);
 * let ret_3: f64 = obj.get_average_time(startStation, endStation);
 */

// [
//   "UndergroundSystem",
//   "checkIn",
//   "checkIn",
//   "checkIn",
//   "checkOut",
//   "checkOut",
//   "checkOut",
//   "getAverageTime",
//   "getAverageTime",
//   "checkIn",
//   "getAverageTime",
//   "checkOut",
//   "getAverageTime"
// ]

// [
//   [],
//   [
//     45,
//     "Leyton",
//     3
//   ],
//   [
//     32,
//     "Paradise",
//     8
//   ],
//   [
//     27,
//     "Leyton",
//     10
//   ],
//   [
//     45,
//     "Waterloo",
//     15
//   ],
//   [
//     27,
//     "Waterloo",
//     20
//   ],
//   [
//     32,
//     "Cambridge",
//     22
//   ],
//   [
//     "Paradise",
//     "Cambridge"
//   ],
//   [
//     "Leyton",
//     "Waterloo"
//   ],
//   [
//     10,
//     "Leyton",
//     24
//   ],
//   [
//     "Leyton",
//     "Waterloo"
//   ],
//   [
//     10,
//     "Waterloo",
//     38
//   ],
//   [
//     "Leyton",
//     "Waterloo"
//   ]
// ]
#[test]
fn test() {
    let mut obj = UndergroundSystem::new();

    obj.check_in(45, "Leyton".into(), 3);
    obj.check_in(32, "Paradise".into(), 8);
    obj.check_in(27, "Leyton".into(), 10);

    obj.check_out(45, "Waterloo".into(), 15);
    obj.check_out(27, "Waterloo".into(), 20);
    obj.check_out(32, "Cambridge".into(), 22);

    println!(
        "{}",
        obj.get_average_time("Paradise".into(), "Cambridge".into())
    );
    println!(
        "{}",
        obj.get_average_time("Leyton".into(), "Waterloo".into())
    );

    obj.check_in(10, "Leyton".into(), 24);
    println!(
        "{}",
        obj.get_average_time("Leyton".into(), "Waterloo".into())
    );

    obj.check_out(10, "Waterloo".into(), 38);
    println!(
        "{}",
        obj.get_average_time("Leyton".into(), "Waterloo".into())
    );
}
