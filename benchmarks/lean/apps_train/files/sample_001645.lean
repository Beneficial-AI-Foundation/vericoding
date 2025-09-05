One of the services provided by an operating system is memory management. The OS typically provides an API for allocating and releasing memory in a process's address space. A process should only read and write memory at addresses which have been allocated by the operating system. In this kata you will implement a simulation of a simple memory manager.

The language you will be using has no low level memory API, so for our simulation we will simply use an array as the process address space. The memory manager constructor will accept an array (further referred to as `memory`) where blocks of indices will be allocated later.

___

# Memory Manager Contract

## allocate(size)

`allocate` reserves a sequential block (sub-array) of `size` received as an argument in `memory`. It should return the index of the first element in the allocated block, or throw an exception if there is no block big enough to satisfy the requirements.

## release(pointer)

`release` accepts an integer representing the start of the block allocated ealier, and frees that block. If the released block is adjacent to a free block, they should be merged into a larger free block. Releasing an unallocated block should cause an exception.

## write(pointer, value)

To support testing this simulation our memory manager needs to support read/write functionality. Only elements within allocated blocks may be written to. The `write` method accepts an index in `memory` and a `value`. The `value` should be stored in `memory` at that index if it lies within an allocated block, or throw an exception otherwise.

## read(pointer)

This method is the counterpart to `write`. Only indices within allocated blocks may be read. The `read` method accepts an index. If the `index` is within an allocated block, the value stored in `memory` at that index should be returned, or an exception should be thrown otherwise.

def MemoryManager.init {α : Type} (memory : List α) : MemoryManager α := sorry
def MemoryManager.allocate {α : Type} (mm : MemoryManager α) (size : Nat) : Option Nat := sorry

def MemoryManager.write {α : Type} (mm : MemoryManager α) (pointer : Nat) (value : α) : MemoryManager α := sorry
def MemoryManager.read {α : Type} (mm : MemoryManager α) (pointer : Nat) : Option α := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
