use vstd::prelude::*;

verus! {

// <vc-helpers>
#[derive(Clone, Copy)]
struct SeqIterator<T> {
    seq: Seq<T>,
    index: nat,
}

impl<T> SeqIterator<T> {
    pub closed spec fn new(seq: Seq<T>) -> Self {
        Self { seq, index: 0 as nat }
    }

    pub fn new(seq: Seq<T>) -> Self {
        Self {
            seq,
            index: 0,
        }
    }

    pub closed spec fn hasNext(&self) -> bool {
        self.index < self.seq.len()
    }

    pub fn hasNext(&self) -> (b: bool)
        ensures b == (self.index < self.seq.len())
    {
        self.index < self.seq.len()
    }

    pub fn next(&mut self) -> (ret: Option<T>)
        decreases self.seq.len() - self.index
        ensures
            self.index == if (old(self).hasNext()) { old(self).index + 1 } else { old(self).index },
            self.seq == old(self).seq,
            match ret {
                Some(t) => {
                    old(self).hasNext() && t == old(self).seq[old(self).index]
                },
                None => {
                    !old(self).hasNext()
                },
            }
    {
        if self.index < self.seq.len() {
            let ret = Some(self.seq[self.index]);
            self.index = self.index + 1;
            ret
        } else {
            None
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn subtract_sequences(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires 
        a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] - b[i],
// </vc-spec>
// <vc-code>
{
    let mut i: nat = 0;
    let mut result = Seq::<int>::new(a.len());
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == a.len(),
            forall|j: int| 0 <= j < i ==> result[j] == a[j] - b[j],
    {
        result = result.update(i, a[i] - b[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}

}