predicate ValidInput(A: int, B: int, C: int)
{
  1 <= A <= 100 && 1 <= B <= 100 && 0 <= C < B
}

predicate IsSolvable(A: int, B: int, C: int)
{
  exists i :: 1 <= i < B && (i * (A % B)) % B == C
}

// <vc-helpers>
lemma EuclidExtended(a: int, b: int) 
  returns (g: int, x: int, y: int)
  requires a > 0 && b > 0
  ensures g == gcd(a, b)
  ensures a*x - b*y == g || a*x + b*y == g
{
  if b == 0 {
    g := a;
    x := 1;
    y := 0;
  } else {
    var q := a / b;
    var r := a % b;
    var g1: int, x1: int, y1: int;
    g1, x1, y1 := EuclidExtended(b, r);
    g := g1;
    x := y1;
    y := x1 - q * y1;
  }
}

function gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
{
  if b == 0 then a else gcd(b, a % b)
}

lemma CongruenceSolvableLemma(A: int, B: int, C: int, g: int)
  requires 1 <= A <= 100 && 1 <= B <= 100 && 0 <= C < B
  requires g == gcd(A % B, B)
  ensures IsSolvable(A, B, C) <==> C % g == 0
{
}

lemma ExistsSolution(A: int, B: int, C: int, x0: int, g: int)
  requires 1 <= A <= B <= 100 && 0 <= C < B
  requires g == gcd(A % B, B) 
  requires C % g == 0
  requires (x0 * (A % B)) % B == g
  ensures exists i :: 1 <= i < B && (i * (A % B)) % B == C
{
  var scale := C / g;
  var i := (x0 * scale) % B;
  if i < 0 {
    i := i + B;
  }
  assert (i * (A % B)) % B == C;
}

lemma EuclidExtendedHelper(a: int, b: int) returns (x: int, y: int)
  requires a > 0 && b > 0
  ensures exists g: int :: g == gcd(a, b) && (a*x - b*y == g || a*x + b*y == g)
{
  var g, x1, y1 := EuclidExtended(a, b);
  x := x1;
  y := y1;
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int) returns (result: string)
  requires ValidInput(A, B, C)
  ensures result == "YES" <==> IsSolvable(A, B, C)
  ensures result == "NO" || result == "YES"
// </vc-spec>
// <vc-code>
{
  var AmodB := A % B;
  if AmodB == 0 {
    if C == 0 {
      result := "YES";
    } else {
      result := "NO";
    }
  } else {
    var g := gcd(AmodB, B);
    if C % g == 0 {
      var x0: int;
      var y0: int;
      x0, y0 := EuclidExtendedHelper(AmodB, B);
      result := "YES";
    } else {
      result := "NO";
    }
  }
}
// </vc-code>

