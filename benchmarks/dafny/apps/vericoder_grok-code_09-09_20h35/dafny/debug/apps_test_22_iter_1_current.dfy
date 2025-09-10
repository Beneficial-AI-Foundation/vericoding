predicate is_s_palindrome(s: string)
{
    var pal := "AHIMOoTUVvWwXxY";

    forall i :: 0 <= i < |s| ==> 
        var j := |s| - 1 - i;
        if i >= j then true
        else
            if s[i] == s[j] then s[i] in pal
            else (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                 (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| >= 1
    ensures result == "TAK" || result == "NIE"
    ensures result == "TAK" <==> is_s_palindrome(s)
// </vc-spec>
// <vc-code>
{
  var pal := "AHIMOoTUVvWwXxY";
  var n := |s|;
  var i := 0;
  while i < (n / 2)
    invariant 0 <= i <= n / 2
    invariant forall k :: 0 <= k < i ==>
        var j := n - 1 - k;
        if k >= j then true
        else
          if s[k] == s[j] then s[k] in pal
          else (s[k] == 'p' && s[j] == 'q') || (s[k] == 'q' && s[j] == 'p') ||
               (s[k] == 'b' && s[j] == 'd') || (s[k] == 'd' && s[j] == 'b')
  {
    var j := n - 1 - i;
    if s[i] == s[j] {
      if !(s[i] in pal) {
        result := "NIE";
        return;
      }
    } else {
      if !((s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
           (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')) {
        result := "NIE";
        return;
      }
    }
    i := i + 1;
  }
  result := "TAK";
}
// </vc-code>

