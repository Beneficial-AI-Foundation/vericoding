method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  // impl-start
  r := 0;
  while cube(r + 1) <= N
    // invariants-start
    invariant cube(r) <= N
    // invariants-end
  {
    r := r + 1;
  }
  // impl-end
}

method is_cube(n: nat) returns (r: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
  // post-conditions-end
{
    // impl-start
    var root := cube_root(n);
    if cube(root) == n {
        r := true;
    } else {
        cube_of_larger_is_larger();
        r := false;
    }
    // impl-end
}

function cube(n: int): int { n * n * n }
// pure-end
lemma cube_of_larger_is_larger()
    ensures forall smaller : int, larger : int :: smaller <= larger ==> cube(smaller) <= cube(larger)
{}
// pure-end
