--  <vc-preamble>
package Np_Argmax_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;
--  </vc-preamble>

--  <vc-spec>
   procedure Argmax (A : Int_Array; Result : out Index_Type) with
     Pre  => A'Length > 0,
     Post => Result in A'Range
             and then (for all I in A'Range =>
                         (if I < Result then A (Result) > A (I)))
             and then (for all I in A'Range =>
                         (if I > Result then A (Result) >= A (I)));

end Np_Argmax_Spec;

package body Np_Argmax_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
   procedure Argmax (A : Int_Array; Result : out Index_Type) is
   begin
      Result := A'First;
      for I in A'Range loop
         if A (I) > A (Result) then
            Result := I;
         end if;
         pragma Loop_Invariant (Result in A'First .. I);
         pragma Loop_Invariant
           (for all J in A'First .. I =>
              (if J < Result then A (Result) > A (J)));
         pragma Loop_Invariant
           (for all J in A'First .. I =>
              (if J > Result then A (Result) >= A (J)));
      end loop;
   end Argmax;
--  </vc-code>

--  <vc-postamble>
end Np_Argmax_Spec;
--  </vc-postamble>
