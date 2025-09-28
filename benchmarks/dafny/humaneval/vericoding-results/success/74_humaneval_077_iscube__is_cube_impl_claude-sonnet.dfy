// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemma to prove cube function is monotonic */
lemma cube_monotonic(i: int, j: int)
  requires 0 <= i <= j
  ensures cube(i) <= cube(j)
{
  if i == j {
    return;
  }
  assert i < j;
  assert i * i * i <= j * j * j;
}

/* helper modified by LLM (iteration 3): Added lemma to prove when cube exceeds n, all larger cubes also exceed n */
lemma cube_exceeds_all_larger(i: int, n: nat)
  requires 0 <= i && cube(i) > n
  ensures forall j :: j >= i ==> cube(j) >= cube(i)
{
  forall j | j >= i
    ensures cube(j) >= cube(i)
  {
    if j >= i {
      cube_monotonic(i, j);
    }
  }
}

/* helper modified by LLM (iteration 3): Added lemma to prove witness exists when cube root found */
lemma cube_witness(i: nat, n: nat)
  requires cube(i) == n
  requires 0 <= i <= n
  ensures exists r :: 0 <= r <= n && n == cube(r)
{
  assert 0 <= i <= n && n == cube(i);
}
// </vc-helpers>

// <vc-spec>
method is_cube(n: nat) returns (r: bool)

  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Added witness lemma call and fixed postcondition proof */
  var i := 0;
  while i * i * i <= n
    invariant 0 <= i
    invariant forall j :: 0 <= j < i ==> cube(j) != n
    invariant forall j :: 0 <= j < i ==> cube(j) < n
  {
    var cubed := i * i * i;
    if cubed == n {
      cube_witness(i, n);
      r := true;
      return;
    }
    cube_monotonic(i, i + 1);
    i := i + 1;
  }
  
  cube_exceeds_all_larger(i, n);
  r := false;
}
// </vc-code>
