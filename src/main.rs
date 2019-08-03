use std::collections::HashMap;
use std::ops::Index;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct Id(String);

impl From<&str> for Id {
    fn from(x: &str) -> Self {
        Id(x.to_string())
    }
}

#[derive(Debug)]
enum Expr {
    Int(i64),
    Var(Id),
    Lam(Id, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
struct TypeIdx(usize);

#[derive(Debug, Clone)]
enum Type {
    Var,                   // type variable
    Int,                   // integer type
    Arr(TypeIdx, TypeIdx), // function type
}

#[derive(Debug, Clone)]
enum Link {
    Parent(TypeIdx), // parent index
    Rank(usize),     // size of tree
}

#[derive(Debug)]
struct UFChunk {
    link: Link,
    ty: Type,
}

impl UFChunk {
    fn new(ty: Type) -> Self {
        UFChunk {
            link: Link::Rank(1),
            ty,
        }
    }
}

#[derive(Debug)]
struct TypeUF {
    nodes: Vec<UFChunk>,
}

impl TypeUF {
    fn new() -> Self {
        TypeUF { nodes: Vec::new() }
    }

    fn add(&mut self, t: Type) -> TypeIdx {
        self.nodes.push(UFChunk::new(t));
        TypeIdx(self.nodes.len() - 1)
    }

    fn bind_var(&mut self, v: &TypeIdx, t: &TypeIdx) {
        if let Link::Rank(ref mut r) = &mut self.nodes[t.0].link {
            *r += 1;
        }
        self.nodes[v.0].link = Link::Parent(t.clone());
    }

    fn bind_ctor(&mut self, c1: &TypeIdx, c2: &TypeIdx) {
        let l1 = self.nodes[c1.0].link.clone();
        let l2 = self.nodes[c2.0].link.clone();
        if let (Link::Rank(r1), Link::Rank(r2)) = (l1, l2) {
            if r1 > r2 {
                self.nodes[c1.0].link = Link::Parent(c2.clone());
                self.nodes[c2.0].link = Link::Rank(r1 + r2);
            } else {
                self.nodes[c2.0].link = Link::Parent(c1.clone());
                self.nodes[c1.0].link = Link::Rank(r1 + r2);
            }
        }
    }

    fn find(&mut self, t: &TypeIdx) -> TypeIdx {
        match self.nodes[t.0].link {
            Link::Rank(_) => t.clone(),
            Link::Parent(idx) => {
                let par = self.find(&idx);
                self.nodes[t.0].link = Link::Parent(par);
                par
            }
        }
    }

    fn len(&self) -> usize {
        self.nodes.len()
    }

    fn naming(
        &mut self,
        root: &TypeIdx,
        idgen: &mut impl Iterator<Item = String>,
        name: &mut Vec<Option<String>>,
        visit: &mut Vec<bool>,
    ) {
        let root = self.find(&root);

        if visit[root.0] {
            // already visited.
            if name[root.0].is_none() {
                // if not naming yet, naming the loop.
                let r = idgen.next().unwrap();
                name[root.0] = Some(r);
            }
            return;
        }

        visit[root.0] = true;

        match self[&root].clone() {
            Type::Var => {
                // naming variable
                let r = idgen.next().unwrap();
                name[root.0] = Some(r);
            }
            Type::Int => {
                () // do nothing
            }
            Type::Arr(l, r) => {
                self.naming(&l, idgen, name, visit);
                self.naming(&r, idgen, name, visit);
            }
        }
    }

    fn to_string(&mut self, root: &TypeIdx, name: &[Option<String>], visit: &mut [bool]) -> String {
        let root = self.find(root);

        if visit[root.0] {
            return name[root.0].clone().unwrap();
        }

        visit[root.0] = true;

        match self[&root].clone() {
            Type::Var => name[root.0].clone().unwrap(),
            Type::Int => "Int".into(),
            Type::Arr(l, r) => {
                let l = self.to_string(&l, name, visit);
                let r = self.to_string(&r, name, visit);
                if let Some(a) = name[root.0].clone() {
                    format!("({} -> {} as {})", l, r, a)
                } else {
                    format!("({} -> {})", l, r)
                }
            }
        }
    }
}

impl Index<&TypeIdx> for TypeUF {
    type Output = Type;

    fn index(&self, idx: &TypeIdx) -> &Self::Output {
        &self.nodes[idx.0].ty
    }
}

struct TypeInfer {
    uf: TypeUF,
}

impl TypeInfer {
    fn new() -> Self {
        TypeInfer { uf: TypeUF::new() }
    }

    fn unify(&mut self, t1: &TypeIdx, t2: &TypeIdx) -> Result<(), ()> {
        let t1 = &self.uf.find(t1);
        let t2 = &self.uf.find(t2);
        if t1 == t2 {
            return Ok(());
        }

        match (&self.uf[t1].clone(), &self.uf[t2].clone()) {
            (Type::Int, Type::Int) => Ok(()),
            (Type::Arr(arg_ty1, ret_ty1), Type::Arr(arg_ty2, ret_ty2)) => {
                self.uf.bind_ctor(t1, t2);
                self.unify(arg_ty1, arg_ty2)?;
                self.unify(ret_ty1, ret_ty2)?;
                Ok(())
            }
            (Type::Var, _) => {
                self.uf.bind_var(t1, t2);
                Ok(())
            }
            (_, Type::Var) => {
                self.uf.bind_var(t2, t1);
                Ok(())
            }
            _ => Err(()),
        }
    }

    fn infer(&mut self, e: &Expr, env: &mut HashMap<Id, TypeIdx>) -> Result<TypeIdx, ()> {
        match e {
            Expr::Int(_) => Ok(self.uf.add(Type::Int)),
            Expr::Var(x) => env.get(x).cloned().ok_or(()),
            Expr::Lam(x, e) => {
                let arg_ty = self.uf.add(Type::Var);
                env.insert(x.clone(), arg_ty);
                let ans_ty = self.infer(e, env)?;
                env.remove(x);
                Ok(self.uf.add(Type::Arr(arg_ty, ans_ty)))
            }
            Expr::App(e1, e2) => {
                let t1 = self.infer(e1, env)?;
                let t2 = self.infer(e2, env)?;
                let ret_ty = self.uf.add(Type::Var);
                let ty = self.uf.add(Type::Arr(t2, ret_ty));
                self.unify(&t1, &ty)?;
                Ok(ret_ty)
            }
        }
    }

    fn typing(&mut self, e: &Expr) -> Result<TypeIdx, ()> {
        self.infer(e, &mut HashMap::new())
    }

    fn print(&mut self, t: &TypeIdx) {
        let mut name = vec![None; self.uf.len()];
        let mut idgen = (97u8..=122).map(|i| String::from_utf8(vec![i]).unwrap());
        self.uf
            .naming(t, &mut idgen, &mut name, &mut vec![false; self.uf.len()]);
        let s = self.uf.to_string(t, &name, &mut vec![false; self.uf.len()]);
        println!("root: {:?}", t);
        println!("UF:[{:#?}]", self.uf);
        println!("name:[{:#?}]", name);
        println!("type:{}", s);
    }
}

fn main() -> Result<(), ()> {
    use Expr::*;
    /*let e1 = Lam(
        "x".into(),
        Box::new(App(Box::new(Var("x".into())), Box::new(Var("x".into())))),
    );
    let e2 = Lam(
        "x".into(),
        Box::new(App(Box::new(Var("x".into())), Box::new(Var("x".into())))),
    );
    let e = App(Box::new(e1), Box::new(e2));*/

    // \x. x (\y. y y x) x
    // \x. (x (\y. (y y) x)) x
    let e0 = Lam(
        "y".into(),
        Box::new(App(
            Box::new(App(Box::new(Var("y".into())), Box::new(Var("y".into())))),
            Box::new(Var("x".into())),
        )),
    );
    let e = Lam(
        "x".into(),
        Box::new(App(
            Box::new(App(Box::new(Var("x".into())), Box::new(e0))),
            Box::new(Var("x".into())),
        )),
    );

    let mut ctx = TypeInfer::new();
    let ty = ctx.typing(&e)?;
    ctx.print(&ty);
    Ok(())
}
