-- Guard patterns in match expressions

-- Simple guard with variable pattern
def isPositive (x : Int) : Bool :=
  match x with
  | n if n > 0 => true
  | _ => false

-- Guard with literal pattern
def checkSpecialValue (x : Nat) : String :=
  match x with
  | 42 if someCondition => "The answer!"
  | 42 => "Just 42"
  | _ => "Something else"

-- Multiple guards
def classifyNumber (x : Int) : String :=
  match x with
  | n if n > 100 => "large"
  | n if n > 10 => "medium"
  | n if n > 0 => "small"
  | 0 => "zero"
  | _ => "negative"

-- Guard with comparison operators
def compareWithThreshold (x y : Nat) : String :=
  match (x, y) with
  | (a, b) if a < b => "first is smaller"
  | (a, b) if a > b => "first is larger"
  | (a, b) if a == b => "equal"
  | _ => "impossible"

-- Guard with boolean expressions
def processValue (x : Nat) (flag : Bool) : String :=
  match x with
  | n if flag && n > 0 => "positive with flag"
  | n if flag => "zero or negative with flag"
  | n if n > 0 => "positive without flag"
  | _ => "zero or negative without flag"

-- Guard with complex conditions
def analyzeData (data : List Nat) (threshold : Nat) : String :=
  match data with
  | [] => "empty"
  | [x] if x >= threshold => "single large element"
  | [x] => "single small element"
  | xs if xs.length > 10 && xs.all (· >= threshold) => "many large elements"
  | xs if xs.length > 10 => "many mixed elements"
  | _ => "few elements"

-- Guard with equality checks
def handleSpecialCases (x : String) (expected : String) : String :=
  match x with
  | s if s == expected => "matches expectation"
  | s if s.length == expected.length => "same length as expected"
  | "" => "empty string"
  | _ => "different"

-- Guard patterns in tuple destructuring
def processPair (pair : Nat × Nat) : String :=
  match pair with
  | (x, y) if x + y > 100 => "large sum"
  | (x, y) if x == y => "equal values"
  | (0, y) => "first is zero"
  | (x, 0) => "second is zero"
  | _ => "regular pair"

-- Guard with range checks
def categorizeAge (age : Nat) : String :=
  match age with
  | n if n >= 65 => "senior"
  | n if n >= 18 => "adult"
  | n if n >= 13 => "teenager"
  | n if n >= 0 => "child"
  | _ => "invalid"

-- Nested patterns with guards (simplified syntax)
def processNestedData (data : (Nat × String) × Bool) : String :=
  match data with
  | ((n, s), flag) if flag && n > 0 && s.length > 0 => "valid active data"
  | ((n, s), flag) if flag => "active but incomplete"
  | ((n, s), _) if n > 0 && s.length > 0 => "inactive but complete"
  | _ => "incomplete or invalid"