// https://www.coursera.org/learn/algorithmic-toolbox/programming/kAiGl/programming-assignment-3-greedy-algorithms

use std::str::FromStr;

fn main() {
    let d = {
        let mut buff = String::new();
        std::io::stdin().read_line(&mut buff).unwrap();
        u32::from_str(&buff.trim()).unwrap()
    };

    let m = {
        let mut buff = String::new();
        std::io::stdin().read_line(&mut buff).unwrap();
        u32::from_str(&buff.trim()).unwrap()
    };

    let number_of_stops = {
        let mut buff = String::new();
        std::io::stdin().read_line(&mut buff).unwrap();
        u32::from_str(&buff.trim()).unwrap()
    };

    let stops = {
        let mut stops = vec![];
        let mut buff = String::new();
        std::io::stdin().read_line(&mut buff).unwrap();
        let mut strs = buff.split_whitespace();

        for _ in 0..number_of_stops {
            stops.push(u32::from_str(strs.next().unwrap()).unwrap());
        }
        stops
    };

    println!("{}", car_fueling(d, m, stops));
}

fn car_fueling(d: u32, m: u32, stops: Vec<u32>) -> i16 {
    let mut current_mile = 0;
    let mut next_stop = 0_usize;
    let mut last_stop: Option<usize> = None;
    let mut number_of_refills = 0;

    loop {
        if current_mile + m >= d {
            return number_of_refills;
        } else if next_stop > stops.len() {
            return -1;
        } else if stops.len() == next_stop || current_mile + m < stops[next_stop] {
            if next_stop == 0 || (last_stop.is_some() && (last_stop.unwrap() == next_stop - 1)) {
                return -1;
            }

            current_mile = stops[next_stop - 1];
            last_stop = Some(next_stop - 1);
            number_of_refills += 1;
        }

        if stops.len() > next_stop + 1 && (stops[next_stop + 1] - stops[next_stop]) > m {
            return -1;
        }

        next_stop += 1;
    }
}

#[test]
fn test_car_fueling() {
    assert_eq!(2, car_fueling(950, 400, vec![200, 375, 550, 750]));
    assert_eq!(-1, car_fueling(10, 3, vec![1, 2, 5, 9]));
    assert_eq!(-1, car_fueling(700, 200, vec![100, 200, 300, 400]));
}
