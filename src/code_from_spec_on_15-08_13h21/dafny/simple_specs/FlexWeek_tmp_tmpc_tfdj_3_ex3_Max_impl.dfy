//IMPL
method Max(a:array<nat>)returns(m:int)
ensures a.Length > 0 ==> forall k :: 0<=k<a.Length ==> m >= a[k]// not strong enough
ensures a.Length == 0 ==> m == -1
ensures a.Length > 0 ==> m in a[..] // finally at the top // approach did not work for recusrive function
{
    if a.Length == 0 {
        m := -1;
    } else {
        m := a[0];
        var i := 1;
        while i < a.Length
            invariant 1 <= i <= a.Length
            invariant m >= 0
            invariant forall k :: 0 <= k < i ==> m >= a[k]
            invariant m in a[..i]
        {
            if a[i] > m {
                m := a[i];
            }
            i := i + 1;
        }
    }
}