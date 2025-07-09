use std::fmt;

use crate::name::Name;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Level {
    pub kind: LevelKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LevelKind {
    Zero,
    Succ(Box<Level>),
    Max(Box<Level>, Box<Level>),
    IMax(Box<Level>, Box<Level>),
    Param(Name),
    MVar(Name),
}

impl Level {
    pub fn zero() -> Self {
        Level {
            kind: LevelKind::Zero,
        }
    }

    pub fn succ(l: Level) -> Self {
        Level {
            kind: LevelKind::Succ(Box::new(l)),
        }
    }

    pub fn max(l1: Level, l2: Level) -> Self {
        Level {
            kind: LevelKind::Max(Box::new(l1), Box::new(l2)),
        }
    }

    pub fn imax(l1: Level, l2: Level) -> Self {
        Level {
            kind: LevelKind::IMax(Box::new(l1), Box::new(l2)),
        }
    }

    pub fn param(name: Name) -> Self {
        Level {
            kind: LevelKind::Param(name),
        }
    }

    pub fn mvar(name: Name) -> Self {
        Level {
            kind: LevelKind::MVar(name),
        }
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.kind, LevelKind::Zero)
    }

    pub fn is_succ(&self) -> bool {
        matches!(self.kind, LevelKind::Succ(_))
    }

    pub fn is_max(&self) -> bool {
        matches!(self.kind, LevelKind::Max(_, _))
    }

    pub fn is_imax(&self) -> bool {
        matches!(self.kind, LevelKind::IMax(_, _))
    }

    pub fn is_param(&self) -> bool {
        matches!(self.kind, LevelKind::Param(_))
    }

    pub fn is_mvar(&self) -> bool {
        matches!(self.kind, LevelKind::MVar(_))
    }

    pub fn normalize(&self) -> Level {
        match &self.kind {
            LevelKind::Max(l1, l2) => {
                let l1 = l1.normalize();
                let l2 = l2.normalize();

                if l1.is_zero() {
                    l2
                } else if l2.is_zero() || l1 == l2 {
                    l1
                } else {
                    Level::max(l1, l2)
                }
            }
            LevelKind::IMax(l1, l2) => {
                let l1 = l1.normalize();
                let l2 = l2.normalize();

                if l2.is_zero() {
                    Level::zero()
                } else if l1.is_zero() {
                    l2
                } else {
                    Level::imax(l1, l2)
                }
            }
            _ => self.clone(),
        }
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            LevelKind::Zero => write!(f, "0"),
            LevelKind::Succ(l) => write!(f, "{l} + 1"),
            LevelKind::Max(l1, l2) => write!(f, "max {l1} {l2}"),
            LevelKind::IMax(l1, l2) => write!(f, "imax {l1} {l2}"),
            LevelKind::Param(name) => write!(f, "{name}"),
            LevelKind::MVar(name) => write!(f, "?{name}"),
        }
    }
}

#[cfg(test)]
mod tests;
