import Sail
namespace S2Bytes
theorem join64 (d : BitVec 64) :
    BitVec.append
      (BitVec.append
        (BitVec.append
          (BitVec.append
            (BitVec.append
              (BitVec.append
                (BitVec.append (d.extractLsb' 56 8) (d.extractLsb' 48 8))
                (d.extractLsb' 40 8))
              (d.extractLsb' 32 8))
            (d.extractLsb' 24 8))
          (d.extractLsb' 16 8))
        (d.extractLsb' 8 8))
      (d.extractLsb' 0 8) = d := by
  simp only [BitVec.append_eq]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 8) (by decide : 56 = 48 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 16) (by decide : 48 = 40 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 24) (by decide : 40 = 32 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 32) (by decide : 32 = 24 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 40) (by decide : 24 = 16 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 48) (by decide : 16 = 8 + 8)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := d) (len₂ := 56) (by decide : 8 = 0 + 8)]
  exact BitVec.extractLsb'_eq_self

@[simp] theorem join64_happend (d : BitVec 64) :
    ((((((d.extractLsb' 56 8 +++ d.extractLsb' 48 8) +++ d.extractLsb' 40 8) +++
      d.extractLsb' 32 8) +++ d.extractLsb' 24 8) +++ d.extractLsb' 16 8) +++
      d.extractLsb' 8 8) +++ d.extractLsb' 0 8 = d := by
  simpa only [BitVec.append_eq] using join64 d
end S2Bytes
