function upper_sum_rec(s: string): int
  // post-conditions-start
  ensures upper_sum_rec(s) >= 0
  // post-conditions-end
{
  // impl-start
  if |s| == 0 then
    0
  else
    var remaining := upper_sum_rec(s[1..]);
    to_int(s[0]) + remaining
  // impl-end
}
function to_int(c: char): int
    ensures 'A' <= c <= 'Z' ==> to_int(c) == c as int
    ensures c < 'A' || c > 'Z' ==> to_int(c) == 0
{
    if 'A' <= c <= 'Z' then c as int else 0
}

// <vc-helpers>
function IsUpperCase(c: char): bool
  ensures IsUpperCase(c) == ('A' <= c <= 'Z')
{
  'A' <= c <= 'Z'
}

function to_int_upper(c: char): int
  ensures to_int_upper(c) == (if IsUpperCase(c) then c as int else 0)
{
  if IsUpperCase(c) then c as int else 0
}

function upper_sum_rec_prefix(s: string, i: int): int
  requires 0 <= i <= |s|
  ensures upper_sum_rec_prefix(s, i) >= 0
{
  if i == 0 then
    0
  else
    upper_sum_rec_prefix(s, i - 1) + to_int_upper(s[i - 1])
}
// </vc-helpers>

// <vc-spec>
method upper_sum(s: string) returns (res: int)
    // post-conditions-start
    ensures res == upper_sum_rec(s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  res := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant res == upper_sum_rec_prefix(s, i)
  {
    var c := s[i];
    res := res + to_int_upper(c);
    i := i + 1;
  }
}
// </vc-code>

