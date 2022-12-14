// use core::ops::BitOr;
// use std::marker::Sized;

use std::fmt::Display;

pub trait IsPathUnit: Eq + std::hash::Hash
{
    fn left() -> Self;
    fn right() -> Self;
}

pub trait IsPath<PathUnit>: Display + Clone + Eq + std::hash::Hash
where
    PathUnit: IsPathUnit,
{
    fn root() -> Self;
    fn push_at_leaf(&mut self, bits: PathUnit, bit_length: usize);
    fn pop_at_root(&mut self, bit_length: usize) -> Self;
    fn pop_at_root_bit(&mut self) -> bool;
    fn join_at_leaf(&mut self, other: Self);
    fn length(&self) -> usize;
    fn as_path_unit(self) -> PathUnit;
}
