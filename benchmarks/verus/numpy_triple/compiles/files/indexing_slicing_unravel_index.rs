/* Converts a flat index or array of flat indices into a tuple of coordinate arrays.

Parameters
----------
indices : array_like
    An integer array whose elements are indices into the flattened version of an array of dimensions shape.
shape : tuple of ints
    The shape of the array to use for unraveling indices.
order : {'C', 'F'}, optional
    Determines whether the indices should be viewed as indexing in row-major (C-style) or column-major (Fortran-style) order.

Returns
-------
unraveled_coords : tuple of ndarray
    Each array in the tuple has the same shape as the indices array.
    
Converts flat indices into multi-dimensional coordinates for a given shape.
This is the inverse operation of ravel_multi_index.

Specification: unravel_index converts flat indices to multi-dimensional coordinates
such that the coordinates are valid for the given shape and represent the correct
positions in the multi-dimensional array. */

use vstd::prelude::*;

verus! {
spec fn spec_shape_product(shape: Seq<nat>) -> nat 
    decreases shape.len()
{
    if shape.len() == 0 {
        1
    } else {
        shape[0] * spec_shape_product(shape.drop_first())
    }
}
fn unravel_index(indices: &Vec<nat>, shape: &Vec<nat>) -> (result: Vec<Vec<nat>>)
    requires 
        shape.len() > 0,
        forall|i: int| 0 <= i < shape.len() ==> shape[i] > 0,
        forall|i: int| 0 <= i < indices.len() ==> indices[i] < spec_shape_product(shape@),
    ensures
        result.len() == indices.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == shape.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < shape.len() ==> result[i][j] < shape[j],
        forall|i: int, j: int| 0 <= i < indices.len() && 0 <= j < indices.len() && i != j && indices[i] != indices[j] ==> result[i] != result[j],
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}