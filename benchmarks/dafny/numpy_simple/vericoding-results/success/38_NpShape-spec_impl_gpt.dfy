// <vc-preamble>
datatype Matrix<T> = Matrix(m: nat, n: nat, data: seq<seq<T>>)

function MatrixSize<T>(matrix: Matrix<T>): nat
{
    matrix.m * matrix.n
}

datatype Arrays = ArrayOne(arr1: seq<real>) | ArrayTwo(arr2: seq<seq<real>>) | ArrayThree(arr3: seq<seq<seq<real>>>)

function ArraysNdim(a: Arrays): nat
{
    match a
    case ArrayOne(_) => 1
    case ArrayTwo(_) => 2
    case ArrayThree(_) => 3
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Product over a sequence of naturals */
function Product(s: seq<nat>): nat
  decreases |s|
{
  if |s| == 0 then 1 else s[0] * Product(s[1..])
}

/* helper modified by LLM (iteration 3): product of a length-1 sequence */
lemma LemmaProductLen1(s: seq<nat>)
  requires |s| == 1
  ensures Product(s) == s[0]
{
  assert |s| > 0;
  assert Product(s) == s[0] * Product(s[1..]);
  assert |s[1..]| == 0;
  assert Product(s[1..]) == 1;
}

/* helper modified by LLM (iteration 3): product of a length-2 sequence equals the product of its elements */
lemma LemmaProductLen2(s: seq<nat>)
  requires |s| == 2
  ensures Product(s) == s[0] * s[1]
{
  assert |s| > 0;
  assert Product(s) == s[0] * Product(s[1..]);
  var t := s[1..];
  assert |t| == 1;
  LemmaProductLen1(t);
  assert Product(t) == t[0];
  assert Product(s) == s[0] * t[0];
  assert t[0] == s[1];
}

/* helper modified by LLM (iteration 3): relate a 2-D shape sequence to total size m*n without invoking methods in expressions */
lemma LemmaProductMatchesSizeForDims(m: nat, n: nat, sh: seq<nat>)
  requires |sh| == 2 && sh[0] == m && sh[1] == n
  ensures Product(sh) == m * n
{
  LemmaProductLen2(sh);
  assert Product(sh) == sh[0] * sh[1];
}
// </vc-helpers>

// <vc-spec>
method {:axiom} ShapeArrays(a: Arrays) returns (result: seq<nat>)
    ensures
        |result| == ArraysNdim(a) &&
        match a {
            case ArrayOne(arr) => |result| == 1 && result[0] == |arr|
            case ArrayTwo(arr) => |result| == 2 && result[0] == |arr| && 
                result[1] == (if |arr| > 0 then |arr[0]| else 0)
            case ArrayThree(arr) => |result| == 3 && result[0] == |arr| && 
                result[1] == (if |arr| > 0 then |arr[0]| else 0) &&
                result[2] == (if |arr| > 0 && |arr[0]| > 0 then |arr[0][0]| else 0)
        }

method {:axiom} ShapeMatrix(a: Matrix<real>) returns (result: seq<nat>)
    ensures
        |result| == 2 &&
        result[0] == a.m &&
        result[1] == a.n
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): construct shape directly to avoid termination issues and prove product property */
  var sh: seq<nat> := [a.m, a.n];
  LemmaProductMatchesSizeForDims(a.m, a.n, sh);
  result := sh;
}
// </vc-code>
