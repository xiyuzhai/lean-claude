" Vim syntax file
" Language: Lean 4
" Maintainer: Lean Analyzer Team

if exists("b:current_syntax")
  finish
endif

" Keywords
syn keyword leanKeyword def theorem lemma axiom constant variable variables parameter parameters
syn keyword leanKeyword universe universes inductive structure class instance namespace section
syn keyword leanKeyword end open export hide include omit precedence reserve infix infixl
syn keyword leanKeyword infixr prefix postfix notation syntax macro macro_rules elab attribute
syn keyword leanKeyword run_cmd check eval reduce example abbrev deriving extends mut
syn keyword leanKeyword if then else match with do let in where by have show from fun λ
syn keyword leanKeyword forall ∀ exists ∃ sorry admit undefined unreachable

" Modifiers
syn keyword leanModifier private protected public export noncomputable partial unsafe opaque

" Types
syn keyword leanType Prop Type Sort Nat Int String Char Bool Unit Empty True False List Array
syn keyword leanType Option Sum Prod IO

" Constants
syn keyword leanConstant true false none some

" Operators
syn match leanOperator "→\|←\|↔\|⟨\|⟩\|∧\|∨\|¬\|⊥\|⊤\|⊂\|⊆\|∈\|∉\|≠\|≤\|≥"
syn match leanOperator ":=\|:\|=\|<\|>\|+\|-\|\*\|/\|%\|\^\||\|\.\|,\|;\|@\|#\|\$\|\?\|!"

" Numbers
syn match leanNumber "\<\d\+\>\|\<0x\x\+\>\|\<0b[01]\+\>"
syn match leanFloat "\<\d\+\.\d*\>\|\<\d*\.\d\+\>"

" Strings
syn region leanString start='"' skip='\\"' end='"' contains=leanEscape
syn region leanChar start="'" skip="\\'" end="'" contains=leanEscape
syn match leanEscape "\\[\\\"'nrt]" contained

" Comments
syn match leanComment "--.*$" contains=leanTodo,@Spell
syn region leanBlockComment start="/-" end="-/" contains=leanBlockComment,leanTodo,@Spell

" Documentation comments
syn region leanDocComment start="/--" end="-/" contains=leanTodo,@Spell

" Todo
syn keyword leanTodo TODO FIXME XXX NOTE contained

" Attributes
syn region leanAttribute start="@\[" end="\]" contains=leanString,leanNumber

" Universes
syn match leanUniverse "Type\*\|Type\s\+\d\+\|Sort\s\+\d\+"

" Identifiers
syn match leanIdentifier "\<[a-zA-Z_][a-zA-Z0-9_']*\>"

" Special identifiers
syn match leanSpecialId "⟨\|⟩\|‹\|›"

" Tactics
syn keyword leanTactic intro intros apply exact refine rfl simp ring norm_num linarith omega
syn keyword leanTactic tauto decide assumption contradiction exfalso cases induction constructor
syn keyword leanTactic left right split use existsi generalize clear revert subst rw rewrite
syn keyword leanTactic calc conv repeat first try all_goals any_goals focus swap rotate iterate

" Define highlighting
hi def link leanKeyword Keyword
hi def link leanModifier StorageClass
hi def link leanType Type
hi def link leanConstant Constant
hi def link leanOperator Operator
hi def link leanNumber Number
hi def link leanFloat Float
hi def link leanString String
hi def link leanChar Character
hi def link leanEscape SpecialChar
hi def link leanComment Comment
hi def link leanBlockComment Comment
hi def link leanDocComment SpecialComment
hi def link leanTodo Todo
hi def link leanAttribute PreProc
hi def link leanUniverse Type
hi def link leanIdentifier Identifier
hi def link leanSpecialId Special
hi def link leanTactic Function

let b:current_syntax = "lean"