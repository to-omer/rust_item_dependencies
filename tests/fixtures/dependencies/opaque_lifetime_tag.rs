struct UnionFind {
    cells: Vec<usize>,
}

impl UnionFind {
    #[doc = "rust-item-dependencies:tag=opaque-lifetime"]
    fn roots(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.cells.len()).filter(|&index| self.cells[index] == index)
    }
}

fn main() {
    let union_find = UnionFind { cells: Vec::new() };
    let _ = union_find.roots().count();
}
