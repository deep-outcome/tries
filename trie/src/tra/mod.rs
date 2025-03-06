#![allow(dead_code)]

/// track strain discrete values
pub mod tsdv {
    pub const NON: u8 = 1;
    pub const TRA: u8 = 2;
    pub const REF: u8 = 4;
    pub const MUT: u8 = 8;
    pub const EMP: u8 = 16;
}

#[repr(u8)]
#[derive(Clone, Debug)]
pub enum TraStrain {
    NonRef = tsdv::NON | tsdv::REF,
    NonMut = tsdv::NON | tsdv::MUT,

    TraEmp = tsdv::TRA | tsdv::EMP,
    TraRef = tsdv::TRA | tsdv::REF,

    #[cfg(test)]
    NonEmp = tsdv::NON | tsdv::EMP,

    #[cfg(test)]
    Unset = 0,
}

impl TraStrain {
    pub fn has(self, f: u8) -> bool {
        self as u8 & f == f
    }
}

#[cfg(test)]
mod tests_of_units {
    use crate::{tsdv, TraStrain};

    #[test]
    fn has_has() {
        for f in [tsdv::NON, tsdv::EMP] {
            assert_eq!(true, TraStrain::has(TraStrain::NonEmp, f));
        }
    }

    #[test]
    fn has_has_not() {
        for f in [tsdv::TRA, tsdv::REF] {
            assert_eq!(false, TraStrain::has(TraStrain::NonEmp, f));
        }
    }

    #[test]
    fn values() {
        use tsdv::*;

        let vals = [
            (TraStrain::NonEmp, [NON, EMP]),
            (TraStrain::NonRef, [NON, REF]),
            (TraStrain::NonMut, [NON, MUT]),
            (TraStrain::TraEmp, [TRA, EMP]),
            (TraStrain::TraRef, [TRA, REF]),
        ];

        for v in vals {
            // dv = discrete value
            for dv in v.1 {
                assert_eq!(
                    true,
                    TraStrain::has(v.0.clone(), dv),
                    "v {:?}, dv {dv}",
                    v.0
                );
            }
        }
    }

    #[test]
    fn unset() {
        assert_eq!(0, TraStrain::Unset as u8);
    }
}

// cargo test --release
