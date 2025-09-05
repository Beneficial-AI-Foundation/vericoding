You are standing on top of an amazing Himalayan mountain. The view is absolutely breathtaking! you want to take a picture on your phone, but... your memory is full again! ok, time to sort through your shuffled photos and make some space...

Given a gallery of photos, write a function to sort through your pictures.
You get a random hard disk drive full of pics, you must return an array with the 5 most recent ones PLUS the next one (same year and number following the one of the last).

You will always get at least a photo and all pics will be in the format `YYYY.imgN`

Examples:
```python
sort_photos["2016.img1","2016.img2","2015.img3","2016.img4","2013.img5"]) ==["2013.img5","2015.img3","2016.img1","2016.img2","2016.img4","2016.img5"]
sort_photos["2016.img1"]) ==["2016.img1","2016.img2"]
```

def Photo := String 
def Year := Nat

def ImgNum := Nat

instance : Inhabited Photo := ⟨""⟩
instance : LT Year := ⟨Nat.lt⟩
instance : LT ImgNum := ⟨Nat.lt⟩
instance : HAdd ImgNum Nat ImgNum := ⟨Nat.add⟩
instance : LT (Year × ImgNum) := ⟨λ a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)⟩

def sort_photos (photos : List Photo) : List Photo :=
  sorry

-- Helper function to parse year from photo string

def parse_year (photo : Photo) : Year := 
  sorry

-- Helper function to parse image number from photo string

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded