import CT1.Tables.Route7
set_option autoImplicit false

/-! CT1 M2, route 7 (first validation consumer): (b) window coverage and (c) no SVE/SME, decided over the
    generated table (ROUTE7-DIT-TABLE.json). Route 7 has no shim: W = the whole run, so G5 is vacuous. -/

namespace CT1.Route7
open CT1.Words CT1.Tables.Route7

theorem table_length : table.length = 22 := by decide

/-- (b) every word of memcpy / memset / memmove is DIT-listed or K4 public control. -/
theorem memcpy_window_listed : windowListed table memcpyWords = true := by decide
theorem memset_window_listed : windowListed table memsetWords = true := by decide
theorem memmove_window_listed : windowListed table memmoveWords = true := by decide

/-- No route-7 word is a `publicConstant` or `shimControl` (every non-branch word is DIT-listed: K4 option (i)). -/
theorem memcpy_nonbranch_dit : memcpyWords.all (fun w => match table.lookup w with
    | some c => c.isDit || c.isPublicControl | none => false) = true := by decide
theorem memset_nonbranch_dit : memsetWords.all (fun w => match table.lookup w with
    | some c => c.isDit || c.isPublicControl | none => false) = true := by decide
theorem memmove_nonbranch_dit : memmoveWords.all (fun w => match table.lookup w with
    | some c => c.isDit || c.isPublicControl | none => false) = true := by decide

/-- (c) no SVE/SME encoding and no SMSTART/SMSTOP/MSR SVCR word. -/
theorem memcpy_no_sve : noSveSme memcpyWords = true := by decide
theorem memset_no_sve : noSveSme memsetWords = true := by decide
theorem memmove_no_sve : noSveSme memmoveWords = true := by decide

/-- Mutant: a word outside the table fails the check (the check is not vacuous). -/
theorem mutant_unlisted : windowListed table (memcpyWords ++ [0xd503415f]) = false := by decide
theorem mutant_sve : noSveSme (memcpyWords ++ [0x04a00000]) = false := by decide

end CT1.Route7

#print axioms CT1.Route7.memmove_window_listed
#print axioms CT1.Route7.memmove_no_sve
