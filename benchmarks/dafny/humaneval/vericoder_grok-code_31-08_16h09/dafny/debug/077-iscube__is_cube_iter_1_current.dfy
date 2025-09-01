method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_cube(n: nat) returns (r: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var x2: nat := 1;
  while x2 <= n && (x2 * x2 <= n / x2)
  {
    x2 := x2 * 2;
  }
  var x := 1;
  var cube := 1;
  while x < x2
  {
    var new_cube := cube + 3 * x * (x + 1) * x + (x + 1) * (x + 1) * (x + 1) - cube;
    x := x * 2;
    cube := new_cube;
  }
  while x > 0
  {
    var cube_low := (x / 2) * (x / 2) * (x / 2);
    if n < cube_low{
      x := x / 2;
    } else if cube >= n {
      break;
    } else {
      x := x - 1;
    }
  }
  r := cube(r) == n;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end