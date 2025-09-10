function is_tandem_repeat(s: seq<char>): bool
{
    if |s| % 2 != 0 then false
    else
        var half_len := |s| / 2;
        var first_half := s[0..half_len];
        var second_half := s[half_len..];
        forall i :: 0 <= i < half_len ==> 
            (first_half[i] == '*' || second_half[i] == '*' || first_half[i] == second_half[i])
}

// <vc-helpers>
predicate is_valid_tandem_sequence(s: seq<char>)
  requires |s| % 2 == 0
{
  var half_len := |s| / 2;
  var first_half := s[0..half_len];
  var second_half := s[half_len..];
  forall i | 0 <= i < half_len :: 
    (first_half[i] == '*' || second_half[i] == '*' || first_half[i] == second_half[i])
}

lemma tandem_sequence_contains_pair(s: seq<char>, i: int, n: int, k: int)
  requires |s| >= 1
  requires k >= 1
  requires 0 <= i < |s| + k
  requires 2 <= n <= |s| + k - i
  requires n % 2 == 0
  requires is_tandem_repeat((s + seq(k, j => '*'))[i..i+n])
  ensures exists p, q :: 0 <= p <= q < n/2 && 
          ((s + seq(k, j => '*'))[i+p] == (s + seq(k, j => '*'))[i+n/2+q] ||
           (s + seq(k, j => '*'))[i+p] == '*' ||
           (s + seq(k, j => '*'))[i+n/2+q] == '*')
{
}

lemma max_tandem_exists(s: seq<char>, k: int, max_len: int)
  requires k >= 1
  requires |s| >= 1
  requires max_len >= 0
  requires max_len % 2 == 0
  requires max_len <= |s| + k
  requires forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 && 
           is_tandem_repeat((s + seq(k, j => '*'))[i..i+n]) ==> n <= max_len
  requires max_len > 0 ==> exists i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 && 
           is_tandem_repeat((s + seq(k, j => '*'))[i..i+n]) && n == max_len
  ensures max_len == 0 ==> forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 ==> 
           !is_tandem_repeat((s + seq(k, j => '*'))[i..i+n])
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: int)
    requires k >= 1
    requires |s| >= 1
    ensures result >= 0
    ensures result % 2 == 0
    ensures result <= |s| + k
    ensures forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 && 
            is_tandem_repeat((s + seq(k, j => '*'))[i..i+n]) ==> n <= result
    ensures result == 0 ==> forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 ==> 
            !is_tandem_repeat((s + seq(k, j => '*'))[i..i+n])
    ensures result > 0 ==> exists i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 && 
            (is_tandem_repeat((s + seq(k, j => '*'))[i..i+n]) && n == result)
// </vc-spec>
// <vc-code>
{
  var T := s + seq(k, j => '*');
  var max_len := 0;
  var n := |T|;
  
  if n % 2 != 0 {
    n := n - 1;
  }
  
  while (n >= 2)
    invariant n >= 0
    invariant n % 2 == 0
    invariant max_len >= 0 && max_len % 2 == 0
    invariant max_len <= |s| + k
    invariant forall i, m :: 0 <= i < |s| + k && 2 <= m <= |s| + k - i && m % 2 == 0 && m > n && 
             is_tandem_repeat(T[i..i+m]) ==> m <= max_len
    invariant max_len > 0 ==> exists i, m :: 0 <= i < |s| + k && 2 <= m <= |s| + k - i && m % 2 == 0 && 
             is_tandem_repeat(T[i..i+m]) && m == max_len
    decreases n
  {
    var found := false;
    var i := 0;
    
    while (i <= |T| - n)
      invariant 0 <= i <= |T| - n + 1
      invariant !found ==> forall j | 0 <= j < i :: !is_tandem_repeat(T[j..j+n])
      invariant found ==> is_tandem_repeat(T[i-1..(i-1)+n])
      decreases |T| - n - i
    {
      if is_tandem_repeat(T[i..i+n]) {
        found := true;
        break;
      }
      i := i + 1;
    }
    
    if found {
      max_len := n;
      break;
    }
    
    n := n - 2;
  }
  
  result := max_len;
}
// </vc-code>

