//! This is terrible, hideous, and ugly. Burn it with fire. We need to make
//! a variable binding abstraction to help us get rid of this boilerplate.
//!
//! There are a number of libraries out there for other languages that abstract
//! away handling locally nameless representations, but I've not yet figured out
//! how to port them to Rust yet:
//!
//! - DBLib: Facilities for working with de Bruijn indices in Coq
//!     - [Blog Post](http://gallium.inria.fr/blog/announcing-dblib/)
//!     - [Github](https://github.com/coq-contribs/dblib)
//! - Unbound: Specify the binding structure of your data type with an
//!   expressive set of type combinators, and Unbound handles the rest!
//!   Automatically derives alpha-equivalence, free variable calculation,
//!   capture-avoiding substitution, and more.
//!     - [Github](https://github.com/sweirich/replib)
//!     - [Hackage](https://hackage.haskell.org/package/unbound)
//! - Unbound-Generics: an independent re-implementation of Unbound but using
//!   GHC.Generics instead of RepLib.
//!     - [Github](http://github.com/lambdageek/unbound-generics)
//!     - [Hackage](https://hackage.haskell.org/package/unbound-generics)
//! - Bound: Bruijn indices for Haskell
//!     - [Blog Post](https://www.schoolofhaskell.com/user/edwardk/bound)
//!     - [Github](https://github.com/ekmett/bound/)
//!     - [Hackage](https://hackage.haskell.org/package/bound)
//! - The Penn Locally Nameless Metatheory Library
//!     - [Github](https://github.com/plclub/metalib)

use std::collections::HashSet;

use syntax::var::LocallyNameless;
use super::*;

impl TermLam {
    pub fn bind(param: Named<Name, Option<RcTerm>>, mut body: RcTerm) -> TermLam {
        body.close(&param.name);

        TermLam {
            unsafe_param: param,
            unsafe_body: body,
        }
    }

    pub fn unbind(self) -> (Named<Name, Option<RcTerm>>, RcTerm) {
        let mut param = self.unsafe_param;
        let mut body = self.unsafe_body;

        // let free_name = Name::fresh(param.name.name()); // FIXME
        let free_name = Name::fresh();
        param.name = free_name.clone();
        body.open(&free_name);

        (param, body)
    }
}

impl TermPi {
    pub fn bind(param: Named<Name, RcTerm>, mut body: RcTerm) -> TermPi {
        body.close(&param.name);

        TermPi {
            unsafe_param: param,
            unsafe_body: body,
        }
    }

    pub fn unbind(self) -> (Named<Name, RcTerm>, RcTerm) {
        let mut param = self.unsafe_param;
        let mut body = self.unsafe_body;

        // let free_name = Name::fresh(param.name.name()); // FIXME
        let free_name = Name::fresh();
        param.name = free_name.clone();
        body.open(&free_name);

        (param, body)
    }
}

impl ValueLam {
    pub fn bind(param: Named<Name, Option<RcValue>>, mut body: RcValue) -> ValueLam {
        body.close(&param.name);

        ValueLam {
            unsafe_param: param,
            unsafe_body: body,
        }
    }

    pub fn unbind(self) -> (Named<Name, Option<RcValue>>, RcValue) {
        let mut param = self.unsafe_param;
        let mut body = self.unsafe_body;

        // let free_name = Name::fresh(param.name.name()); // FIXME
        let free_name = Name::fresh();
        param.name = free_name.clone();
        body.open(&free_name);

        (param, body)
    }
}

impl ValuePi {
    pub fn bind(param: Named<Name, RcValue>, mut body: RcValue) -> ValuePi {
        body.close(&param.name);

        ValuePi {
            unsafe_param: param,
            unsafe_body: body,
        }
    }

    pub fn unbind(self) -> (Named<Name, RcValue>, RcValue) {
        let mut param = self.unsafe_param;
        let mut body = self.unsafe_body;

        // let free_name = Name::fresh(param.name.name()); // FIXME
        let free_name = Name::fresh();
        param.name = free_name.clone();
        body.open(&free_name);

        (param, body)
    }
}

// TODO: Would be nice for this to be more polymorphic
pub fn unbind2(
    lam: TermLam,
    pi: ValuePi,
) -> (
    Named<Name, Option<RcTerm>>,
    RcTerm,
    Named<Name, RcValue>,
    RcValue,
) {
    let mut lam_param = lam.unsafe_param;
    let mut lam_body = lam.unsafe_body;
    let mut pi_param = pi.unsafe_param;
    let mut pi_body = pi.unsafe_body;

    // let free_name = Name::fresh(lam_param.name.name()); // FIXME
    let free_name = Name::fresh();
    lam_param.name = free_name.clone();
    pi_param.name = free_name.clone();

    lam_body.open(&free_name);
    pi_body.open(&free_name);

    (lam_param, lam_body, pi_param, pi_body)
}

impl LocallyNameless for RcTerm {
    type Name = Name;

    fn close_at(&mut self, level: Debruijn, name: &Name) {
        match *Rc::make_mut(&mut self.inner) {
            Term::Ann(_, ref mut expr, ref mut ty) => {
                expr.close_at(level, name);
                ty.close_at(level, name);
            },
            Term::Universe(_, _) => {},
            Term::Var(_, ref mut var) => var.close_at(level, name),
            Term::Lam(_, ref mut lam) => {
                lam.unsafe_param.close_at(level, name);
                lam.unsafe_body.close_at(level.succ(), name);
            },
            Term::Pi(_, ref mut pi) => {
                pi.unsafe_param.close_at(level, name);
                pi.unsafe_body.close_at(level.succ(), name);
            },
            Term::App(_, ref mut fn_expr, ref mut arg_expr) => {
                fn_expr.close_at(level, name);
                arg_expr.close_at(level, name);
            },
    }
    }

    fn open_at(&mut self, level: Debruijn, name: &Name) {
        match *Rc::make_mut(&mut self.inner) {
            Term::Ann(_, ref mut expr, ref mut ty) => {
                expr.open_at(level, name);
                ty.open_at(level, name);
            },
            Term::Universe(_, _) => {},
            Term::Var(_, ref mut var) => var.open_at(level, name),
            Term::Lam(_, ref mut lam) => {
                lam.unsafe_param
                    .inner
                    .as_mut()
                    .map(|param_ty| param_ty.open_at(level, name));
                lam.unsafe_body.open_at(level.succ(), name);
            },
            Term::Pi(_, ref mut pi) => {
                pi.unsafe_param.open_at(level, name);
                pi.unsafe_body.open_at(level.succ(), name);
            },
            Term::App(_, ref mut fn_expr, ref mut arg_expr) => {
                fn_expr.open_at(level, name);
                arg_expr.open_at(level, name);
            },
    }
}
}

impl RcTerm {
    pub fn subst(&mut self, name: &Name, x: &RcTerm) {
        *self = match *Rc::make_mut(&mut self.inner) {
            Term::Ann(_, ref mut expr, ref mut ty) => {
                expr.subst(name, x);
                ty.subst(name, x);
                return;
            },
            Term::Universe(_, _) => return,
            Term::Var(_, Var::Free(ref n)) if n == name => x.clone(),
            Term::Var(_, Var::Free(_)) | Term::Var(_, Var::Bound(_)) => return,
            Term::Lam(_, ref mut lam) => {
                lam.unsafe_param
                    .inner
                    .as_mut()
                    .map(|param| param.subst(name, x));
                lam.unsafe_body.subst(name, x);
                return;
            },
            Term::Pi(_, ref mut pi) => {
                pi.unsafe_param.inner.subst(name, x);
                pi.unsafe_body.subst(name, x);
                return;
            },
            Term::App(_, ref mut fn_expr, ref mut arg_expr) => {
                fn_expr.subst(name, x);
                arg_expr.subst(name, x);
                return;
            },
        };
    }

    fn visit_vars<F: FnMut(&Var<Name, Debruijn>)>(&self, on_var: &mut F) {
        match *self.inner {
            Term::Ann(_, ref expr, ref ty) => {
                expr.visit_vars(on_var);
                ty.visit_vars(on_var);
            },
            Term::Universe(_, _) => {},
            Term::Var(_, ref var) => on_var(var),
            Term::Lam(_, ref lam) => {
                if let Some(ref param) = lam.unsafe_param.inner {
                    param.visit_vars(on_var);
                }
                lam.unsafe_body.visit_vars(on_var);
            },
            Term::Pi(_, ref pi) => {
                pi.unsafe_param.inner.visit_vars(on_var);
                pi.unsafe_body.visit_vars(on_var);
            },
            Term::App(_, ref fn_expr, ref arg_expr) => {
                fn_expr.visit_vars(on_var);
                arg_expr.visit_vars(on_var);
            },
        };
    }

    pub fn free_vars(&self) -> HashSet<Name> {
        let mut free_vars = HashSet::new();
        self.visit_vars(&mut |var| match *var {
            Var::Bound(_) => {},
            Var::Free(ref name) => {
                free_vars.insert(name.clone());
            },
        });
        free_vars
    }
}

impl LocallyNameless for RcValue {
    type Name = Name;

    fn close_at(&mut self, level: Debruijn, name: &Name) {
        match *Rc::make_mut(&mut self.inner) {
            Value::Universe(_) => {},
            Value::Var(ref mut var) => var.close_at(level, name),
            Value::Lam(ref mut lam) => {
                lam.unsafe_param.close_at(level, name);
                lam.unsafe_body.close_at(level.succ(), name);
            },
            Value::Pi(ref mut pi) => {
                pi.unsafe_param.close_at(level, name);
                pi.unsafe_body.close_at(level.succ(), name);
            },
            Value::App(ref mut fn_expr, ref mut arg_expr) => {
                fn_expr.close_at(level, name);
                arg_expr.close_at(level, name);
            },
        }
    }

    fn open_at(&mut self, level: Debruijn, name: &Name) {
        match *Rc::make_mut(&mut self.inner) {
            Value::Universe(_) => {},
            Value::Var(ref mut var) => var.open_at(level, name),
            Value::Lam(ref mut lam) => {
                lam.unsafe_param.open_at(level, name);
                lam.unsafe_body.open_at(level.succ(), name);
            },
            Value::Pi(ref mut pi) => {
                pi.unsafe_param.open_at(level, name);
                pi.unsafe_body.open_at(level.succ(), name);
            },
            Value::App(ref mut fn_expr, ref mut arg_expr) => {
                fn_expr.open_at(level, name);
                arg_expr.open_at(level, name);
            },
        }
    }
}

impl RcValue {
    pub fn subst(&mut self, name: &Name, x: &RcValue) {
        *self = match *Rc::make_mut(&mut self.inner) {
            Value::Universe(_) => return,
            Value::Var(Var::Free(ref n)) if n == name => x.clone(),
            Value::Var(Var::Free(_)) | Value::Var(Var::Bound(_)) => return,
            Value::Lam(ref mut lam) => {
                lam.unsafe_param
                    .inner
                    .as_mut()
                    .map(|param| param.subst(name, x));
                lam.unsafe_body.subst(name, x);
                return;
            },
            Value::Pi(ref mut pi) => {
                pi.unsafe_param.inner.subst(name, x);
                pi.unsafe_body.subst(name, x);
                return;
            },
            Value::App(ref mut fn_expr, ref mut arg_expr) => {
                fn_expr.subst(name, x);
                arg_expr.subst(name, x);
                return;
            },
        };
    }
}
