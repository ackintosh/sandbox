#[cfg(test)]
mod tests {
    use bitflags::bitflags;

    bitflags! {
        struct Flags: u32 {
            const A = 0b001;
            const B = 0b010;
            const C = 0b100;
            const ABC = Self::A.bits | Self::B.bits | Self::C.bits;
        }
    }

    #[test]
    fn it_works() {
        let e1 = Flags::A | Flags::C;
        let e2 = Flags::B | Flags::C;
        // union
        assert_eq!((e1 | e2), Flags::ABC);

        let ab = Flags::A | Flags::B;
        let ac = Flags::A | Flags::C;
        assert!((Flags::A | Flags::B | Flags::C).contains(ab));
        assert!((Flags::A | Flags::B | Flags::C).contains(ac));
    }
}
