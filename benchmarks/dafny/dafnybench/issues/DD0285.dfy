// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Max(a:array<nat>)returns(m:int)
ensures a.Length > 0 ==> forall k :: 0<=k<a.Length ==> m >= a[k]// not strong enough
ensures a.Length == 0 ==> m == -1
ensures a.Length > 0 ==> m in a[..] // finally at the top // approach did not work for recusrive function
// </vc-spec>
// <vc-code>
{
    if(a.Length == 0){
        return -1;
    }
    assert a.Length > 0;
    var i := 0;
    m := a[0];
    assert m in a[..]; // had to show that m is in a[..], otherwise how could i assert for it

    while(i < a.Length)
    invariant 0<=i<=a.Length
    invariant forall k :: 0<=k<i ==> m >= a[k]// Not strong enough
    invariant m in a[..] // again i  the array
    // invariant 0 < i <= a.Length ==> (ret_max(a,i-1) == m)
    {
        if(a[i] >= m){
            m:= a[i];
        }
        i := i+1;
    }

    assert m in a[..]; //
}
// </vc-code>
