
use crate::BitTree::Definition::*;
use crate::Node::NodeKind::Definition::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathInTile::*;

use std::string::*;
use std::fmt;
use std::vec::*;
use std::collections::HashMap;
use std::hash::Hash;

/// A single bit-tree.
///
/// Layout:
/// 1
/// 2 3
/// 4 5 6 7
/// 8 ... 15
/// 16 ... 31
///
#[derive(PartialEq, Eq, Hash)]
pub struct BitTree32
{
    pub bits: u32
}

impl BitTree32
{

}

impl IsBitTree for BitTree32
{
    fn full_height() -> usize
    {
        5
    }

    fn slice_height() -> usize
    {
        4
    }

    fn from<NK: IsNodeKind, P : IsPath<W>, W : IsPathUnit>(path: PathInTile<Self,P,W,NK>) -> BitTree32
    {
        let mut p = path.0;
        let mut tree : u32 = 1;

        while p.length() > 0
        {
            let direction = p.pop_at_root_bit();
            let tree = tree * 2 + 1 + (direction as u32);
        }

        BitTree32 {bits: tree}
    }
    fn empty() -> BitTree32
    {
        BitTree32 {bits: 0}
    }
}


