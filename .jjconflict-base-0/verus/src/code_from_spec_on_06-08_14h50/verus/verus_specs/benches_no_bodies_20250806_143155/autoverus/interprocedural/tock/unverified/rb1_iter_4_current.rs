use vstd::prelude::*;
use vstd::view::View;

pub fn main() {}

verus! {
    pub open spec fn ex_saturating_sub_spec(a: int, b: int) -> (ret: nat)
    {
        if (a > b) {
            (a - b) as nat
        } else {
            0
        }
    }

    #[verifier::external_fn_specification]
    pub fn ex_saturating_sub(a: usize, b: usize) -> (ret: usize)
    ensures
        ex_saturating_sub_spec(a as int, b as int) == ret as int
    {
        if a > b {
            a - b
        } else {
            0
        }
    }

    pub trait Queue<T> {
        /// Returns true if there are any items in the queue, false otherwise.
        fn has_elements(&self) -> (ret: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
            requires
                self.inv()
            ensures
                self.inv()
        ;

        /// Returns true if the queue is full, false otherwise.
        fn is_full(&self) -> (ret: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
            requires
                self.inv()
            ensures
                self.inv()
        ;

        /// Returns how many elements are in the queue.
        fn len(&self) -> (ret: usize)
{
    return false;  // TODO: Remove this line and implement the function body
}
            requires
                self.inv()
            ensures
                self.inv()
        ;

        /// If the queue isn't full, add a new element to the back of the queue.
        /// Returns whether the element was added.
        fn enqueue(&mut self, val: T) -> (ret: bool)
{
    return false;  // TODO: Remove this line and implement the function body
}
            requires
                old(self).inv()
            ensures
                self.inv()
        ;

        /// Remove the element from the front of the queue.
        fn dequeue(&mut self) -> (ret: Option<T>)
{
    return false;  // TODO: Remove this line and implement the function body
}
            requires
                old(self).inv()
            ensures
                self.inv()
        ;

        /// Invariant for the queue.
        spec fn inv(&self) -> bool;

        spec fn capacity_spec(&self) -> nat;
    }

    pub struct RingBuffer<T> {
        ring: Vec<T>,
        head: usize,
        tail: usize,
    }

    impl<T: Copy> View for RingBuffer<T> {
        type V = Seq<T>;

        closed spec fn view(&self) -> Self::V {
            let len = if self.tail >= self.head {
                self.tail - self.head
            } else {
                self.ring.len() - self.head + self.tail
            };

            Seq::new(len as nat, |i| {
                let index = (self.head + i) % self.ring.len() as int;
                self.ring[index]
            })
        }
    }

    impl<T: Copy> Queue<T> for RingBuffer<T> {
        closed spec fn inv(&self) -> bool
        {
            &&& self.head < self.ring.len()
            &&& self.tail < self.ring.len()
            &&& self.ring.len() > 1
        }

        closed spec fn capacity_spec(&self) -> nat
        {
            (self.ring.len() - 1) as nat
        }

        fn has_elements(&self) -> (result: bool)
            requires
                self.inv()
            ensures
                self.inv(),
                result == (self@.len() != 0),
        {
            /* code modified by LLM (iteration 1): Fixed trait method implementation */
            self.head != self.tail
        }

        fn is_full(&self) -> (ret: bool)
            requires
                self.inv()
            ensures
                self.inv(),
                ret == (self@.len() == self.capacity_spec())
        {
            /* code modified by LLM (iteration 1): Fixed trait method implementation */
            (self.tail + 1) % self.ring.len() == self.head
        }

        fn len(&self) -> (ret: usize)
            requires
                self.inv()
            ensures
                self.inv(),
                ret == self@.len(),
        {
            /* code modified by LLM (iteration 1): Fixed trait method implementation */
            if self.tail >= self.head {
                self.tail - self.head
            } else {
                self.ring.len() - self.head + self.tail
            }
        }

        fn enqueue(&mut self, val: T) -> (succ: bool)
            requires
                old(self).inv()
            ensures
                self.inv(),
                old(self)@.len() == old(self).capacity_spec() <==> !succ, /* Full failed iff. */
                self.capacity_spec() == old(self).capacity_spec(), /* Capacity unchanged */
                succ == (self@.len() == old(self)@.len() + 1), /* Length increment, we need it here to avoid recommendation not met below */
                succ ==> (self@.len() <= self.capacity_spec()), /* No exceeds capacity */
                succ ==> (self@.last() == val), /* Push to last */
                forall |i: int| 0 <= i < old(self)@.len() ==> self@[i] == old(self)@[i], /* Prior unchanged */
        {
            /* code modified by LLM (iteration 1): Fixed trait method implementation */
            if self.is_full() {
                false
            } else {
                self.ring.set(self.tail, val);
                self.tail = (self.tail + 1) % self.ring.len();
                true
            }
        }

        fn dequeue(&mut self) -> (ret: Option<T>)
            requires
                old(self).inv()
            ensures
                self.inv(),
                self.capacity_spec() == old(self).capacity_spec(), /* Capacity unchanged */
                old(self)@.len() == 0 <==> ret == None::<T>, /* Empty failed iff. */
                old(self)@.len() > 0 <==> ret != None::<T>, /* Non-empty succ iff. */
                if let Some(val) = ret {
                    self@.len() + 1 == old(self)@.len() && /* Length decrement */
                    val == old(self)@.first() && /* Pop from first */
                    (forall |i: int| 0 <= i < self@.len() ==> self@[i] == old(self)@[i + 1]) /* Shifted */
                } else {
                    self@.len() == old(self)@.len() /* Failed condition */
                },
        {
            /* code modified by LLM (iteration 1): Fixed trait method implementation */
            if self.has_elements() {
                let val = self.ring[self.head];
                self.head = (self.head + 1) % self.ring.len();
                Some(val)
            } else {
                None
            }
        }
    }

    impl<T: Copy> RingBuffer<T> {
        pub fn new(ring: Vec<T>) -> (ret: RingBuffer<T>)
            requires
                ring.len() > 1
            ensures
                ret.capacity_spec() == ring.len() as nat - 1,
                ret@.len() == 0,
                ret.inv(),
        {
            RingBuffer {
                ring,
                head: 0,
                tail: 0,
            }
        }

        /// Returns the number of elements that can be enqueued until the ring buffer is full.
        pub fn available_len(&self) -> (ret: usize)
            requires
                self.inv()
            ensures
                ret == self.capacity_spec() - self@.len()
        {
            /* code modified by LLM (iteration 1): Added proper ensures clause and implementation */
            self.capacity_spec() as usize - self.len()
        }
    }

    #[verifier::loop_isolation(false)]
    fn test_enqueue_dequeue_generic(len: usize, value: i32, iterations: usize)
        requires
            len < usize::MAX - 1,
            iterations * 2 < usize::MAX,
    {
        if len > 1 {
            let mut vec = Vec::new();
            let mut i = 0;
            while i < len
                invariant
                    vec.len() == i,
                    i <= len,
            {
                vec.push(0i32);
                i = i + 1;
            }
            
            let mut buffer = RingBuffer::new(vec);
            
            let mut j = 0;
            while j < iterations
                invariant
                    j <= iterations,
                    buffer.inv(),
            {
                let _ = buffer.enqueue(value);
                let _ = buffer.dequeue();
                j = j + 1;
            }
        }
    }
}