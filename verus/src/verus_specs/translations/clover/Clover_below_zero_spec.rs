pub fn below_zero(operations: Seq<int>) -> (s: Vec<int>, result: bool)
    ensures
        s.len() == operations.len() + 1,
        s[0] == 0,
        forall|i: int| 0 <= i < s.len() - 1 ==> s[i + 1] == s[i] + operations[i],
        result == true ==> (exists|i: int| 1 <= i <= operations.len() && s[i] < 0),
        result == false ==> forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
{
}