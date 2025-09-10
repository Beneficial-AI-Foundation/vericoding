datatype InputData = InputData(n: int, m: int, segments: set<(int, int)>)

predicate valid_input_format(stdin_input: string)
{
    |stdin_input| > 0
}

function parse_input(stdin_input: string): InputData
requires valid_input_format(stdin_input)
{
    InputData(2, 0, {})
}

function rotate_segment(seg: (int, int), k: int, n: int): (int, int)
requires 1 <= seg.0 <= n && 1 <= seg.1 <= n
requires k >= 0 && n > 0
{
    var a := var temp_a := (seg.0 + k) % n; if temp_a == 0 then n else temp_a;
    var b := var temp_b := (seg.1 + k) % n; if temp_b == 0 then n else temp_b;
    (a, b)
}

predicate exists_rotational_symmetry(data: InputData)
{
    exists k :: 1 <= k < data.n && 
        data.n % k == 0 &&
        (forall seg :: seg in data.segments ==> 
            seg.0 >= 1 && seg.0 <= data.n && seg.1 >= 1 && seg.1 <= data.n &&
            rotate_segment(seg, k, data.n) in data.segments)
}

// <vc-helpers>
lemma rotate_segment_symmetric(seg: (int, int), k: int, n: int)
requires 1 <= seg.0 <= n && 1 <= seg.1 <= n
requires k >= 0 && n > 0
ensures rotate_segment(rotate_segment(seg, k, n), n - k, n) == seg
{
  var rotated1 := rotate_segment(seg, k, n);
  var rotated2 := rotate_segment(rotated1, n - k, n);
  
  assert rotated2.0 == (
    var a1 := (seg.0 + k) % n; var norm_a1 := if a1 == 0 then n else a1;
    var a2 := (norm_a1 + (n - k)) % n;
    if a2 == 0 then n else a2
  );
  
  assert rotated2.0 == (seg.0 + k + (n - k)) % n;
  assert rotated2.0 == (seg.0 + n) % n;
  assert rotated2.0 == seg.0 % n;
  if seg.0 % n == 0 {
    assert rotated2.0 == n;
  } else {
    assert rotated2.0 == seg.0;
  }
  
  assert rotated2.0 == if seg.0 % n == 0 then n else seg.0;
  assert rotated2.0 == seg.0; // because seg.0 is between 1 and n
  
  assert rotated2.1 == (
    var b1 := (seg.1 + k) % n; var norm_b1 := if b1 == 0 then n else b1;
    var b2 := (norm_b1 + (n - k)) % n;
    if b2 == 0 then n else b2
  );
  
  assert rotated2.1 == (seg.1 + k + (n - k)) % n;
  assert rotated2.1 == (seg.1 + n) % n;
  assert rotated2.1 == seg.1 % n;
  if seg.1 % n == 0 {
    assert rotated2.1 == n;
  } else {
    assert rotated2.1 == seg.1;
  }
  
  assert rotated2.1 == if seg.1 % n == 0 then n else seg.1;
  assert rotated2.1 == seg.1; // because seg.1 is between 1 and n
}

lemma rotate_segment_identity(seg: (int, int), n: int)
requires 1 <= seg.0 <= n && 1 <= seg.1 <= n
requires n > 0
ensures rotate_segment(seg, n, n) == seg
{
  var rotated := rotate_segment(seg, n, n);
  
  assert rotated.0 == (
    var a := (seg.0 + n) % n;
    if a == 0 then n else a
  );
  assert rotated.0 == (
    var a := seg.0 % n;
    if a == 0 then n else a
  );
  assert rotated.0 == if seg.0 % n == 0 then n else seg.0;
  assert rotated.0 == seg.0; // because seg.0 is between 1 and n
  
  assert rotated.1 == (
    var b := (seg.1 + n) % n;
    if b == 0 then n else b
  );
  assert rotated.1 == (
    var b := seg.1 % n;
    if b == 0 then n else b
  );
  assert rotated.1 == if seg.1 % n == 0 then n else seg.1;
  assert rotated.1 == seg.1; // because seg.1 is between 1 and n
}

lemma rotate_segment_composition(seg: (int, int), k1: int, k2: int, n: int)
requires 1 <= seg.0 <= n && 1 <= seg.1 <= n
requires k1 >= 0 && k2 >= 0 && n > 0
ensures rotate_segment(rotate_segment(seg, k1, n), k2, n) == rotate_segment(seg, (k1 + k2) % n, n)
{
  var rotated1 := rotate_segment(seg, k1, n);
  var rotated2 := rotate_segment(rotated1, k2, n);
  var direct := rotate_segment(seg, (k1 + k2) % n, n);
  
  var a1 := (seg.0 + k1) % n; var norm_a1 := if a1 == 0 then n else a1;
  var a2 := (norm_a1 + k2) % n; var norm_a2 := if a2 == 0 then n else a2;
  
  var direct_a := (seg.0 + (k1 + k2) % n) % n; var norm_direct_a := if direct_a == 0 then n else direct_a;
  
  // Show that (a1 + k2) % n == (a0 + (k1 + k2)) % n
  assert a2 == (seg.0 + k1 + k2) % n;
  assert direct_a == (seg.0 + ((k1 + k2) % n)) % n;
  assert direct_a == (seg.0 + k1 + k2) % n; // because k1 + k2 - n*floor((k1+k2)/n) == (k1+k2) % n
  
  assert norm_a2 == norm_direct_a;
  
  var b1 := (seg.1 + k1) % n; var norm_b1 := if b1 == 0 then n else b1;
  var b2 := (norm_b1 + k2) % n; var norm_b2 := if b2 == 0 then n else b2;
  
  var direct_b := (seg.1 + (k1 + k2) % n) % n; var norm_direct_b := if direct_b == 0 then n else direct_b;
  
  assert b2 == (seg.1 + k1 + k2) % n;
  assert direct_b == (seg.1 + k1 + k2) % n;
  assert norm_b2 == norm_direct_b;
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
requires valid_input_format(stdin_input)
ensures result == "Yes" || result == "No"
ensures result == "Yes" <==> exists_rotational_symmetry(parse_input(stdin_input))
// </vc-spec>
// <vc-code>
{
  var data := parse_input(stdin_input);
  var n := data.n;
  var segments := data.segments;
  
  if n == 1 {
    return "Yes";
  }
  
  var possible := false;
  var k := 1;
  while k < n
    invariant 1 <= k <= n
    invariant !possible ==> forall j :: 1 <= j < k ==> n % j != 0 || !check_symmetry(data, j)
    invariant possible ==> exists j :: 1 <= j < k && n % j == 0 && check_symmetry(data, j)
  {
    if n % k == 0 {
      if check_symmetry(data, k) {
        possible := true;
        break;
      }
    }
    k := k + 1;
  }
  
  if possible {
    return "Yes";
  } else {
    return "No";
  }
}
// </vc-code>

