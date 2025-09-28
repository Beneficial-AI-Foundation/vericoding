// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Complex number type for FFT results */
#[derive(PartialEq, Eq)]
pub struct Complex {
    /* Real part */
    pub re: int,
    /* Imaginary part */
    pub im: int,
}

impl Complex {
    pub open spec fn zero() -> Complex {
        Complex { re: 0, im: 0 }
    }
    
    pub open spec fn add(self, other: Complex) -> Complex {
        Complex { re: self.re + other.re, im: self.im + other.im }
    }
    
    pub open spec fn mul(self, other: Complex) -> Complex {
        Complex { 
            re: self.re * other.re - self.im * other.im, 
            im: self.re * other.im + self.im * other.re 
        }
    }
}

/* Convert int to Complex */
spec fn int_to_complex(x: int) -> Complex {
    Complex { re: x, im: 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix butterfly_spec implementation and fft_recursive_spec proof */
spec fn is_power_of_two(n: nat) -> bool {
    n > 0 && (n & (n - 1)) == 0
}

spec fn log2(n: nat) -> nat
    requires
        is_power_of_two(n),
    decreases n,
{
    if n == 1 {
        0
    } else {
        1 + log2(n / 2)
    }
}

spec fn butterfly_spec(x: Complex, y: Complex, w: Complex) -> (Complex, Complex)
    ensures
        result.0 == x.add(w.mul(y)),
        result.1 == x.add(Complex { re: -1, im: 0 }.mul(w.mul(y))),
{
    (x.add(w.mul(y)), x.add(Complex { re: -1, im: 0 }.mul(w.mul(y))))
}

proof fn fft_recursive_spec(input: Seq<Complex>, n: nat, level: nat) -> Seq<Complex>
    requires
        is_power_of_two(n),
        level <= log2(n),
        input.len() == n,
    ensures
        result.len() == n,
        result[0].im == 0,
{
    if n == 1 {
        input
    } else {
        let half = n / 2;
        let even = input.subrange(0, half);
        let odd = input.subrange(half, n);
        let even_transformed = fft_recursive_spec(even, half, level - 1);
        let odd_transformed = fft_recursive_spec(odd, half, level - 1);
        
        let mut result = Seq::empty();
        let angle = -2 * level as int * 3141592653589793238 / n as int;
        let w = Complex { re: angle, im: 0 };
        
        let mut i = 0;
        while i < half
            invariant
                i <= half,
                result.len() == 2 * i,
                forall|idx: int| 0 <= idx < i ==> {
                    let (b_even, b_odd) = butterfly_spec(even_transformed[idx], odd_transformed[idx], w);
                    result[idx] == b_even,
                    result[i + idx] == b_odd
                },
        {
            let (b_even, b_odd) = butterfly_spec(even_transformed[i], odd_transformed[i], w);
            result = result.push(b_even);
            result = result.push(b_odd);
            i += 1;
        }
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn rfft2(a: Vec<Vec<i8>>) -> (result: Vec<Vec<Complex>>)
    requires 
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i]@.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i]@.len() == a[0]@.len(),
    ensures
        result.len() == a.len(),
        forall|k: int| 0 <= k < result.len() ==> 
            #[trigger] result[k]@.len() == (a[0]@.len() / 2) + 1,
        /* DC component is real (imaginary part is zero) */
        result[0]@[0].im == 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix compilation error with missing semicolon */
{
    let rows = a.len();
    let cols_int = a[0]@.len();
    let result_size = (cols_int / 2) + 1;
    
    let mut result_var = Vec::<Vec<Complex>>::new();
    let mut i = 0;
    
    while i < rows
        invariant
            i <= rows,
            result_var@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result_var[k]@.len() == result_size,
    {
        let mut row_input = Vec::<Complex>::new();
        let mut j = 0;
        
        while j < cols_int
            invariant
                j <= cols_int,
                row_input@.len() == j,
                forall|k: int| 0 <= k < j ==> row_input@[k] == int_to_complex(a[i]@[k] as int),
        {
            row_input.push(Complex { re: a[i][j] as i32 as int, im: 0 });
            j += 1;
        }
        
        let mut result_row = Vec::<Complex>::new();
        
        proof {
            let cols_nat = cols_int as nat;
            assert(is_power_of_two(cols_nat));
            let level = log2(cols_nat);
            let transformed = fft_recursive_spec(row_input@, cols_nat, level);
            
            let mut k = 0;
            while k < result_size
                invariant
                    k <= result_size,
                    result_row@.len() == k,
                    forall|idx: int| 0 <= idx < k ==> result_row@[idx] == transformed[idx],
            {
                result_row.push(Complex { re: transformed[k].re, im: transformed[k].im });
                k += 1;
            }
            
            assert(transformed[0].im == 0);
        }
        
        result_var.push(result_row);
        i += 1;
    }
    
    proof {
        assert(result_var@[0]@[0].im == 0);
    }
    
    result_var
}
// </vc-code>


}
fn main() {}