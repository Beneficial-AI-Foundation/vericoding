pub fn Main() {
}

pub fn H(a: &[i32], c: &[i32], n: usize, j: usize)
    requires(j < n == a.len() == c.len())
{
}

pub fn K(a: &[i32], c: &[i32], n: usize)
    requires(n <= a.len() && n <= c.len())
{
}

pub fn L(a: &[i32], c: &[i32], n: usize)
    requires(n <= a.len() == c.len())
{
}

pub fn M_prime(a: &[i32], c: &[i32], m: usize, n: usize, k: usize, l: usize)
    requires(k + m <= a.len())
    requires(l + n <= c.len())
{
}