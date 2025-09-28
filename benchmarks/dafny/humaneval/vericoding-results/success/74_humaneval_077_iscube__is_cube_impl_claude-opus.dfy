// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemmas to help prove properties about cube function */
lemma CubeMonotonic(a: nat, b: nat)
  requires a <= b
  ensures cube(a) <= cube(b)
{
  // Proof by calculation
}

lemma CubeStrictlyIncreasing(a: nat)
  ensures cube(a) < cube(a + 1)
{
  // a^3 < (a+1)^3 = a^3 + 3a^2 + 3a + 1
  assert cube(a + 1) == a * a * a + 3 * a * a + 3 * a + 1;
  assert cube(a + 1) > cube(a);
}

lemma CubeLargerImpliesArgLarger(a: nat, b: nat)
  requires cube(a) > b
  ensures forall j :: j >= a ==> cube(j) >= cube(a) > b
{
  forall j | j >= a
    ensures cube(j) >= cube(a)
  {
    if j > a {
      CubeMonotonic(a, j);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method is_cube(n: nat) returns (r: bool)

  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): simplified loop and added explicit assertions for postconditions */
  var i := 0;
  r := false;
  
  while i * i * i <= n
    invariant 0 <= i <= n + 1
    invariant forall j :: 0 <= j < i ==> cube(j) != n
    invariant !r
    decreases n + 1 - i
  {
    if i * i * i == n {
      r := true;
      assert 0 <= i <= n;
      assert n == cube(i);
      assert exists k :: 0 <= k <= n && n == cube(k);
      return;
    }
    i := i + 1;
  }
  
  // At this point: i * i * i > n and we haven't found a cube root
  assert i * i * i > n;
  assert forall j :: 0 <= j < i ==> cube(j) != n;
  
  // For j >= i: cube(j) >= cube(i) > n
  forall j | i <= j <= n
    ensures cube(j) != n
  {
    if j >= i {
      CubeMonotonic(i, j);
      assert cube(j) >= cube(i) > n;
    }
  }
  
  assert forall j :: 0 <= j <= n ==> cube(j) != n;
}
// </vc-code>
