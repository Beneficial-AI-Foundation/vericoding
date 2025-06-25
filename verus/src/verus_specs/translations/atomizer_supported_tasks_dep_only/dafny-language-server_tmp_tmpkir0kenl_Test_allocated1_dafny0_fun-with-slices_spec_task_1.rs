pub fn seqIntoArray<A>(s: Seq<A>, a: &mut Array<A>, index: nat) 
    requires 
        index + s.len() <= a.len()
    ensures 
        a@ == old(a@).subrange(0, index as int) + s + old(a@).subrange((index + s.len()) as int, old(a@).len() as int)
{
}