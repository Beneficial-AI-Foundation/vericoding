use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindPositionOfElement(a: Vec<int>, Element: nat, n1: nat, s1: Seq<int>) -> (Position: int, Count: nat)
    requires
        n1 == s1.len() && 0 <= n1 <= a.len(),
        forall i:: 0<= i < s1.len() ==> a.spec_index(i) == s1.spec_index(i)
    ensures
        Position == -1 || Position >= 1,
        s1.len() != 0 && Position >= 1 ==> exists i:: 0 <= i < s1.len() && s1.spec_index(i) == Element
{
    let mut position: int = -1;
    let mut count: nat = 0;
    let mut i: usize = 0;
    
    while i < n1
        invariant
            0 <= i <= n1,
            n1 == s1.len(),
            position == -1 || position >= 1,
            count <= i,
            position == -1 ==> forall j:: 0 <= j < i ==> s1.spec_index(j) != Element,
            position >= 1 ==> exists j:: 0 <= j < i && s1.spec_index(j) == Element,
            count == (forall j:: 0 <= j < i ==> if s1.spec_index(j) == Element { 1 } else { 0 }).fold_left(0, |acc, x| acc + x)
    {
        if a[i] == Element {
            if position == -1 {
                position = (i + 1) as int;
            }
            count = count + 1;
        }
        i = i + 1;
    }
    
    (position, count)
}

}