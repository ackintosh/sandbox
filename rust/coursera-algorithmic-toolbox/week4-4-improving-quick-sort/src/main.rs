fn main() {
    let mut input = read_line(read_num());
    quick_sort(&mut input);
    for n in input {
        print!("{} ", n);
    }
}

fn read_num() -> u64 {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    buff.trim().parse::<u64>().unwrap()
}

fn read_line(number_of_elements: u64) -> Vec<u64> {
    let mut buff = String::new();
    std::io::stdin().read_line(&mut buff).unwrap();
    let mut strs = buff.split_whitespace();

    let mut nums = vec![];
    for _ in 0..number_of_elements {
        nums.push(strs.next().unwrap().parse::<u64>().unwrap());
    }
    nums
}

fn quick_sort(input: &mut Vec<u64>) {
    let r = input.len() - 1;
    _quick_sort(input, 0, r);
}

fn _quick_sort(input: &mut Vec<u64>, l: usize, r: usize) {
    if l >= r {
        return;
    }
    // let pivot = input.first().unwrap(); // TODO: randomize
    let pivot = (l + r) / 2;
    swap(input, l, pivot);

    // let m = two_way(input, l, r);
    let (k, p) = three_way(input, l, r);

    if k != 0 {
        _quick_sort(input, l, k - 1);
    }
    _quick_sort(input, p + 1, r);
}

fn swap(input: &mut Vec<u64>, a: usize, b: usize) {
    let tmp = input[a];
    input[a] = input[b];
    input[b] = tmp;
}

// https://www.toptal.com/developers/sorting-algorithms/quick-sort-3-way
// left < pivot
// middle = pivot
// right > pivot
fn three_way(input: &mut Vec<u64>, l: usize, r: usize) -> (usize, usize) {
    let mut i = l;
    let mut k = l; // start of `right`
    let mut p = r; // start of `middle`

    // move the pivot to the tail of elements.
    //   -> r == pivot
    swap(input, l, r);

    while i < p {
        if input[i] == input[r] {
            swap(input, i, p - 1);
            p -= 1;
        } else if input[i] < input[r] {
            swap(input, i, k);
            k += 1;
            i += 1;
        } else {
            i += 1;
        }
    }

    // println!("{:?}, {}, {}", input, k, p);
    let distance = p - k;
    for pp in p..=r {
        for d in 0..distance {
            swap(input, pp - d, pp - (d + 1));
        }
    }

    (k, k + r - p)
}
