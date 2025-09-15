// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 3): Added lemma for cube function increasing to help prove postcondition */
lemma CubeIncreasing() ensures forall x, y :: 0 <= x < y ==> cube(x) < cube(y) {}
// </vc-helpers>

// <vc-spec>
method is_cube(n: nat) returns (r: bool)

  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 3): Added invariant to loop and call to lemma to help prove postcondition */
var root: nat := 0;
while cube(root) < n
  invariant 0 <= root
  invariant forall r :: 0 <= r < root ==> cube(r) != n
{
  root := root + 1;
}
CubeIncreasing();
r := cube(root) == n;
}
// </vc-code>
