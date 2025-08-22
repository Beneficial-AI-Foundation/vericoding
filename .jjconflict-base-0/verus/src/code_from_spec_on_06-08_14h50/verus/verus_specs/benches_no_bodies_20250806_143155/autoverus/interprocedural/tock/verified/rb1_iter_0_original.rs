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
    return 0;  // TODO: Remove this line and implement the function body
    }

    pub trait Queue<T> {
        /// Returns true if there are any items in the queue, false otherwise.
        fn has_elements(&self) -> (ret: bool)
            requires
                self.inv()
            ensures
                self.inv()
        ;

        /// Returns true if the queue is full, false otherwise.
        fn is_full(&self) -> (ret: bool)
            requires
                self.inv()
            ensures
                self.inv()
        ;

        /// Returns how many elements are in the queue.
        fn len(&self) -> (ret: usize)
            requires
                self.inv()
            ensures
                self.inv()
        ;

        /// If the queue isn't full, add a new element to the back of the queue.
        /// Returns whether the element was added.
        fn enqueue(&mut self, val: T) -> (ret: bool)
            requires
                old(self).inv()
            ensures
                self.inv()
        ;

        /// Remove the element from the front of the queue.
        fn dequeue(&mut self) -> (ret: Option<T>)
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
    return false;  // TODO: Remove this line and implement the function body
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

    /// This function says that for any `x` and `y`, there are two
    /// possibilities for the sum `x % n + y % n`: (1) It's in the range
    /// `[0, n)` and it's equal to `(x + y) % n`. (2) It's in the range
    /// `[n, n + n)` and it's equal to `(x + y) % n + n`.
    pub open spec fn mod_auto_plus(n: int) -> bool
        recommends
            n > 0,
    {
        forall|x: int, y: int|
            {
                let z = (x % n) + (y % n);
                ((0 <= z < n && #[trigger] ((x + y) % n) == z) || (n <= z < n + n && ((x + y) % n) == z
                    - n))
            }
    }

    /// This function says that for any `x` and `y`, there are two
    /// possibilities for the difference `x % n - y % n`: (1) It's in the
    /// range `[0, n)` and it's equal to `(x - y) % n`. (2) It's in the
    /// range `[-n, 0)` and it's equal to `(x + y) % n - n`.
    pub open spec fn mod_auto_minus(n: int) -> bool
        recommends
            n > 0,
    {
        forall|x: int, y: int|
            {
                let z = (x % n) - (y % n);
                ((0 <= z < n && #[trigger] ((x - y) % n) == z) || (-n <= z < 0 && ((x - y) % n) == z
                    + n))
            }
    }

    /// This function states various useful properties about the modulo
    /// operator when the divisor is `n`.
    pub open spec fn mod_auto(n: int) -> bool
        recommends
            n > 0,
    {
        &&& (n % n == 0 && (-n) % n == 0)
        &&& (forall|x: int| #[trigger] ((x % n) % n) == x % n)
        &&& (forall|x: int| 0 <= x < n <==> #[trigger] (x % n) == x)
        &&& mod_auto_plus(n)
        &&& mod_auto_minus(n)
    }

    /// Proof of `mod_auto(n)`, which states various useful properties
    /// about the modulo operator when the divisor is the positive number
    /// `n`
    pub proof fn lemma_mod_auto(n: int)
        requires
            n > 0,
        ensures
            mod_auto(n),
    {
        admit()
    }

    /// forall m n, m > 0 -> n > 0 -> m < n -> m % n = m
    proof fn lemma_mod_le(m: int, n: int)
        requires
            m >= 0,
            n > 0,
            m < n
        ensures
            m % n == m
    {
        assert(m >= 0 && n > 0 && m < n ==> m % n == m) by {
            lemma_mod_auto(n)
        };
    }

    proof fn lemma_rb_first_head<T: Copy>(buf: &RingBuffer<T>)
        requires
            buf.inv(),
            buf@.len() > 0,
        ensures
            buf@.first() =~= buf.ring[buf.head as int]
    {
        if buf.head > 0 {
            assert(buf.head < buf.ring.len());
            assert(buf.head as int % buf.ring.len() as int == buf.head) by {
                lemma_mod_le(buf.head as int, buf.ring.len() as int)
            }
        } else {
            assert(buf.head == 0);
            assert(buf@.first() =~= buf.ring[0]);
        }
    }

    proof fn lemma_rb_last_tail_intro1<T: Copy>(buf: &RingBuffer<T>)
        requires
            buf.inv(),
            buf@.len() > 0,
            buf.tail > 0,
        ensures
            buf@.last() =~= buf.ring[(buf.tail - 1) as int]
    {

        lemma_mod_auto(buf.ring.len() as int);

        assert((buf.head + buf@.len() - 1) % buf.ring.len() as int == buf.tail - 1);
    }

    proof fn lemma_rb_last_tail_intro2<T: Copy>(buf: &RingBuffer<T>)
        requires
            buf.inv(),
            buf@.len() > 0,
            buf.tail == 0,
        ensures
            buf@.last() =~= buf.ring[buf.ring.len() - 1]
    {
        lemma_mod_auto(buf.ring.len() as int);
        assert((buf.head + buf@.len() - 1) % buf.ring.len() as int == buf.ring.len() - 1);
    }

    proof fn lemma_rb_last_tail<T: Copy>(buf: &RingBuffer<T>)
        requires
            buf.inv(),
            buf@.len() > 0
        ensures
            buf.tail == 0 ==> buf@.last() =~= buf.ring[buf.ring.len() - 1],
            buf.tail > 0 ==> buf@.last() =~= buf.ring[(buf.tail - 1) as int]
    {
        if buf.tail > 0 {
            lemma_rb_last_tail_intro1(buf)
        } else if buf.tail == 0 {
            lemma_rb_last_tail_intro2(buf)
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
            ensures
                result == (self@.len() != 0),
        {
    return false;  // TODO: Remove this line and implement the function body
        }

        fn is_full(&self) -> (ret: bool)
            ensures
                ret == (self@.len() == self.capacity_spec())
        {
    return false;  // TODO: Remove this line and implement the function body
        }

        fn len(&self) -> (ret: usize)
            ensures
                ret == self@.len(),
        {
    return 0;  // TODO: Remove this line and implement the function body
        }

        fn enqueue(&mut self, val: T) -> (succ: bool)
            ensures
                old(self)@.len() == old(self).capacity_spec() <==> !succ, /* Full failed iff. */
                self.capacity_spec() == old(self).capacity_spec(), /* Capacity unchanged */
                succ == (self@.len() == old(self)@.len() + 1), /* Length increment, we need it here to avoid recommendation not met below */
                succ ==> (self@.len() <= self.capacity_spec()), /* No exceeds capacity */
                succ ==> (self@.last() == val), /* Push to last */
                forall |i: int| 0 <= i < old(self)@.len() ==> self@[i] == old(self)@[i], /* Prior unchanged */
        {
    return false;  // TODO: Remove this line and implement the function body
        }

        fn dequeue(&mut self) -> (ret: Option<T>)
            ensures
                self.capacity_spec() == old(self).capacity_spec(), /* Capacity unchanged */
                old(self)@.len() == 0 <==> ret == None::<T>, /* Empty failed iff. */
                old(self)@.len() > 0 <==> ret != None::<T>, /* Non-empty succ iff. */
                if let Some(val) = ret {
    return None;  // TODO: Remove this line and implement the function body
                } else {
                    self@.len() == old(self)@.len() /* Failed condition */
                },
        {
            proof {
                lemma_mod_auto(self.ring.len() as int)
            }

            if self.has_elements() {
                let val = self.ring[self.head];

                assert(val == self@.first()) by {
                    lemma_rb_first_head(self)
                };

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
    assume(false);  // TODO: Replace with appropriate return value of type RingBuffer<T>
        }

        /// Returns the number of elements that can be enqueued until the ring buffer is full.
        pub fn available_len(&self) -> (ret: usize)
            requires
                self.inv()
        {
    return 0;  // TODO: Remove this line and implement the function body
        }
    }

    #[verifier::loop_isolation(false)]
    fn test_enqueue_dequeue_generic(len: usize, value: i32, iterations: usize)
        requires
            len < usize::MAX - 1,
            iterations * 2 < usize::MAX,
    {
    // TODO: Remove this comment and implement the function body
    }
}