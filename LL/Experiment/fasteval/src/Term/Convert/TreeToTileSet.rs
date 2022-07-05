
use std::hash::*;
use std::collections::HashMap;

use crate::AlgebraLL::MutMonoid::Definition::*;
use crate::Path::Definition::*;
use crate::NodePath::Definition::*;
use crate::Term::Tree::Definition::*;
use crate::TileSet::Definition::*;
use crate::TileSet::Instance::MutMonoid::*;
use crate::Tile::Example::LamAppTile::*;
use crate::Node::NodeKindGroup::Example::LamAppNKG::*;
use crate::BitTree::Variant::BitTree32::Definition::*;



type MyTileSet<P,W> = TileSet1<LamAppTile<BitTree32>,BitTree32,P,W,LamAppNKG>;

pub fn encode<Path,W>(ts: &TreeTerm) -> MyTileSet<Path,W> where
    Path : IsPath<W>,
    W : IsPathUnit + Clone
{
    encode_(ts,&Path::root()).0
}


fn encode_<Path,W>(ts: &TreeTerm, curpath_immut: &Path) -> (MyTileSet<Path,W>, HashMap<String,Vec<Path>>) where
    Path : IsPath<W>,
    W : IsPathUnit + Clone
{
    let mut curpath = curpath_immut.clone();
    println!("Encoding, curpath={}", curpath);
    match ts {
        TreeTerm::Λ(var,term) =>
        {
            curpath.push_at_leaf(W::left(), 1);
            let (mut t_, mut vars) = encode_(term, &curpath);
            let var_paths = match vars.remove(var) {
                None => vec![],
                Some(a) => a
            };
            // println!("Term: {ts}, path: {curpath}");

            // t_.λ.push((curpath,var_paths));
            println!("==============================");
            println!("pushing lam @ {curpath_immut} to\n{t_}");
            t_.append_single(NodePath::new(curpath, LamAppNKG::Lam));
            println!("result\n{t_}");
            (t_, vars)
        },
        TreeTerm::App(t,s) =>
        {
            // create the left and right paths
            let mut path_l = curpath.clone();
            let mut path_r = curpath.clone();
            path_l.push_at_leaf(W::left(), 1);
            path_r.push_at_leaf(W::right(), 1);

            // call myself recursively
            let (mut t_, mut tvars) = encode_(t, &path_l);
            let (mut s_, mut svars) = encode_(s, &path_r);
            // println!("Term: {ts}, path: {curpath}");
            println!("==============================");
            println!("pushing app @ {curpath_immut} to\n{t_}");
            t_.append_single(NodePath::new(curpath, LamAppNKG::App));
            println!("pushing rhs to\n{t_}");
            t_.append(s_);
            println!("result\n{t_}");
            // merge_vec_hashmaps(&mut tvars, &mut svars);
            (t_, tvars)
        },
        TreeTerm::Var(s) =>
        {
            let mut vars = HashMap::new();
            vars.insert(s.clone(), vec![curpath]);
            (TileSet1::empty(), vars)
        },
        TreeTerm::Invalid() => (TileSet1::empty(), HashMap::new())
    }
}



