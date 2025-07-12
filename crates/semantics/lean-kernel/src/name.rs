use std::fmt;

use eterned::BaseCoword;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Name {
    Anonymous,
    Str(Box<Name>, BaseCoword),
    Num(Box<Name>, u64),
}

impl Name {
    pub fn anonymous() -> Self {
        Name::Anonymous
    }

    pub fn str(prefix: Name, s: impl Into<BaseCoword>) -> Self {
        Name::Str(Box::new(prefix), s.into())
    }

    pub fn num(prefix: Name, n: u64) -> Self {
        Name::Num(Box::new(prefix), n)
    }

    pub fn mk_simple(s: impl Into<BaseCoword>) -> Self {
        Name::str(Name::anonymous(), s)
    }

    pub fn is_anonymous(&self) -> bool {
        matches!(self, Name::Anonymous)
    }

    pub fn is_atomic(&self) -> bool {
        match self {
            Name::Anonymous => true,
            Name::Str(prefix, _) | Name::Num(prefix, _) => prefix.is_anonymous(),
        }
    }

    pub fn components(&self) -> Vec<String> {
        let mut components = Vec::new();
        let mut current = self;

        loop {
            match current {
                Name::Anonymous => break,
                Name::Str(prefix, s) => {
                    components.push(s.to_string());
                    current = prefix;
                }
                Name::Num(prefix, n) => {
                    components.push(n.to_string());
                    current = prefix;
                }
            }
        }

        components.reverse();
        components
    }

    /// Join a base name with a relative name
    pub fn join_relative(base: &Name, relative: &Name) -> Name {
        let relative_components = relative.components();
        let mut result = base.clone();

        for component in relative_components {
            if component.parse::<u64>().is_ok() {
                if let Ok(num) = component.parse::<u64>() {
                    result = Name::num(result, num);
                }
            } else {
                result = Name::str(result, component);
            }
        }

        result
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Name::Anonymous => write!(f, "[anonymous]"),
            _ => {
                let components = self.components();
                write!(f, "{}", components.join("."))
            }
        }
    }
}

impl From<&str> for Name {
    fn from(s: &str) -> Self {
        if s.is_empty() {
            Name::anonymous()
        } else {
            let parts: Vec<&str> = s.split('.').collect();
            let mut name = Name::anonymous();
            for part in parts {
                if let Ok(num) = part.parse::<u64>() {
                    name = Name::num(name, num);
                } else {
                    name = Name::str(name, part);
                }
            }
            name
        }
    }
}

#[cfg(test)]
mod tests;
