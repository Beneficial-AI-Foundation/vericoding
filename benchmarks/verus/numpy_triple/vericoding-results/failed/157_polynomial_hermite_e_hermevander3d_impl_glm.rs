// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed ensures clause syntax */
fn hermite_poly_rec(k: int, t: f64) -> (result: f64)
    decreases k
    ensures
        result == hermite_poly(k, t),
{
    if k <= 0 {
        1.0
    } else if k == 1 {
        t
    } else {
        let h_km1 = hermite_poly_rec(k - 1, t);
        let h_km2 = hermite_poly_rec(k - 2, t);
        t * h_km1 - (k - 1) as f64 * h_km2
    }
}
// </vc-helpers>

// <vc-spec>
spec fn hermite_poly(k: int, t: f64) -> f64
    decreases k
{
    if k <= 0 {
        1.0
    } else if k == 1 {
        t
    } else {

        1.0
    }
}

fn hermevander3d(x: Vec<f64>, y: Vec<f64>, z: Vec<f64>, deg: Vec<u8>) -> (result: Vec<Vec<f64>>)
    requires 
        x.len() == y.len(),
        y.len() == z.len(),
        deg.len() == 3,
        deg[0] as int >= 0 && deg[1] as int >= 0 && deg[2] as int >= 0,
    ensures
        result.len() == x.len(),
        forall |p: int| 0 <= p < result.len() ==> {
            let x_deg = deg[0] as int;
            let y_deg = deg[1] as int; 
            let z_deg = deg[2] as int;
            let order = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
            &&& #[trigger] result[p].len() == order
            &&& (order > 0 ==> result[p][0] == 1.0)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed &&& to && in invariants */
{
    let x_deg = deg[0] as int;
    let y_deg = deg[1] as int;
    let z_deg = deg[2] as int;
    let order = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
    
    let mut result = Vec::with_capacity(x.len());
    
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall |p: int| 0 <= p < i ==> {
                let x_deg = deg[0] as int;
                let y_deg = deg[1] as int; 
                let z_deg = deg[2] as int;
                let order = (x_deg + 1) * (y_deg + 1) * (z_deg + 1);
                (result[p].len() == order) && (order > 0 ==> result[p][0] == 1.0)
            },
        decreases x.len() - i
    {
        let mut row = Vec::with_capacity(order);
        
        let mut idx = 0;
        while idx < order
            invariant
                0 <= idx <= order,
                row.len() == idx,
                (idx > 0 ==> row[0] == 1.0),
            decreases order - idx
        {
            let mut k = 0;
            let mut found = false;
            let mut i_deg = 0;
            let mut j_deg = 0;
            let mut l_deg = 0;
            
            while k <= x_deg && !found
                invariant
                    0 <= k <= x_deg + 1,
                    !found ==> {
                        forall |i: int| 0 <= i < k ==> {
                            forall |j: int| 0 <= j <= y_deg ==> {
                                forall |l: int| 0 <= l <= z_deg ==> {
                                    i * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1) + l != idx
                                }
                            }
                        }
                    },
                    found ==> {
                        0 <= i_deg <= x_deg &&
                        0 <= j_deg <= y_deg &&
                        0 <= l_deg <= z_deg &&
                        i_deg * (y_deg + 1) * (z_deg + 1) + j_deg * (z_deg + 1) + l_deg == idx
                    },
                decreases (if found { 0 } else { x_deg - k + 1 })
            {
                let mut j = 0;
                while j <= y_deg && !found
                    invariant
                        0 <= j <= y_deg + 1,
                        !found ==> {
                            forall |jj: int| 0 <= jj < j ==> {
                                forall |l: int| 0 <= l <= z_deg ==> {
                                    k * (y_deg + 1) * (z_deg + 1) + jj * (z_deg + 1) + l != idx
                                }
                            }
                        },
                        found ==> {
                            0 <= i_deg <= x_deg &&
                            0 <= j_deg <= y_deg &&
                            0 <= l_deg <= z_deg &&
                            k * (y_deg + 1) * (z_deg + 1) + j_deg * (z_deg + 1) + l_deg == idx
                        },
                    decreases (if found { 0 } else { y_deg - j + 1 })
                {
                    let mut l = 0;
                    while l <= z_deg && !found
                        invariant
                            0 <= l <= z_deg + 1,
                            !found ==> {
                                forall |ll: int| 0 <= ll < l ==> {
                                    k * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1) + ll != idx
                                }
                            },
                            found ==> {
                                0 <= i_deg <= x_deg &&
                                0 <= j_deg <= y_deg &&
                                0 <= l_deg <= z_deg &&
                                k * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1) + l_deg == idx
                            },
                        decreases (if found { 0 } else { z_deg - l + 1 })
                    {
                        let pos = k * (y_deg + 1) * (z_deg + 1) + j * (z_deg + 1) + l;
                        if pos == idx {
                            i_deg = k;
                            j_deg = j;
                            l_deg = l;
                            found = true;
                        }
                        l += 1;
                    }
                    j += 1;
                }
                k += 1;
            }
            
            let h_x = hermite_poly_rec(i_deg, x[i]);
            let h_y = hermite_poly_rec(j_deg, y[i]);
            let h_z = hermite_poly_rec(l_deg, z[i]);
            let value = h_x * h_y * h_z;
            row.push(value);
            
            idx += 1;
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}