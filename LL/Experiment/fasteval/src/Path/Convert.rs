
use crate::BitTree::Definition::*;
use crate::Node::NodeKind::Definition::*;
use crate::Path::Definition::*;
use crate::Path::Wrapper::PathInTile::*;
use crate::Path::Wrapper::PathToTile::*;


pub fn split_raw_path<BT,P,W,NK>(p : &P) -> (PathToTile<BT,P,W>, PathInTile<BT,P,W,NK>) where
    BT : IsBitTree,
    P : IsPath<W>,
    W : IsPathUnit,
    NK : IsNodeKind
{
    let l = p.length();
    let mut path_in_tile_length = l % BT::slice_height();
    if path_in_tile_length < NK::slice_shift()
    {
        path_in_tile_length += BT::slice_height();
    }
    let path_to_tile_length = l - path_in_tile_length;
    let mut path = p.clone();
    let path_to_tile = path.pop_at_root(path_to_tile_length);
    let path_in_tile = path;

    println!("Splitting path: {p}\npath_in_tile_length: {path_in_tile_length}\npath_to_tile: {path_to_tile}\npath_in_tile: {path_in_tile}");
    println!("Slice_shift: {}", NK::slice_shift());
    // println!(" => where bits: {}, length: {}", path_in_tile.0, path_in_tile.1);

    (PathToTile::new(path_to_tile), PathInTile::new(path_in_tile))
}




