--  <vc-preamble>
package Np_Clip_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;
--  </vc-preamble>

--  <vc-spec>
   procedure Clip
     (A       : Int_Array;
      Min_Val : Value_Type;
      Max_Val : Value_Type;
      Result  : out Int_Array)
   with
     Pre  => Min_Val < Max_Val
             and then Result'First = A'First and then Result'Last = A'Last,
     Post => (for all I in A'Range =>
                (if A (I) < Min_Val then Result (I) = Min_Val
                 elsif A (I) > Max_Val then Result (I) = Max_Val
                 else Result (I) = A (I)));

end Np_Clip_Spec;

package body Np_Clip_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
   procedure Clip
     (A       : Int_Array;
      Min_Val : Value_Type;
      Max_Val : Value_Type;
      Result  : out Int_Array)
   is
   begin
      Result := (others => 0);
      for I in A'Range loop
         if A (I) < Min_Val then
            Result (I) := Min_Val;
         elsif A (I) > Max_Val then
            Result (I) := Max_Val;
         else
            Result (I) := A (I);
         end if;
         pragma Loop_Invariant
           (for all J in A'First .. I =>
              (if A (J) < Min_Val then Result (J) = Min_Val
               elsif A (J) > Max_Val then Result (J) = Max_Val
               else Result (J) = A (J)));
      end loop;
   end Clip;
--  </vc-code>

--  <vc-postamble>
end Np_Clip_Spec;
--  </vc-postamble>
