use iced::{Column, Container, Element, Row, Sandbox, Settings, Text, TextInput};

pub fn run() {
    State::run(Settings::default())
}

#[derive(Debug, Clone)]
pub enum Message {
    InputChanged(String),
    InputSubmit,
}

pub struct State {
    globals: pikelet::lang::core::Globals,
    input: iced::text_input::State,
    input_value: String,
}

impl Sandbox for State {
    type Message = Message;

    fn new() -> State {
        State {
            globals: pikelet::lang::core::Globals::default(),
            input: iced::text_input::State::default(),
            input_value: "".to_owned(),
        }
    }

    fn title(&self) -> String {
        "Pikelet".to_owned()
    }

    fn update(&mut self, message: Message) {
        match message {
            Message::InputChanged(value) => {
                self.input_value = value;
            }
            Message::InputSubmit => {
                // TODO: execute expression
                self.input_value.clear();
            }
        }
    }

    fn view(&mut self) -> Element<Message> {
        let State {
            globals,
            input,
            input_value,
        } = self;

        Container::new(
            Column::new()
                .push(Text::new("Hi this is Pikelet!"))
                // TODO: Move to separate window?
                .push(Text::new("Globals:"))
                .push(
                    globals
                        .entries()
                        .fold(Column::new(), |column, (name, (r#type, term))| {
                            column.push({
                                let entry = Row::new()
                                    .push(Text::new(name))
                                    .push(Text::new(" : "))
                                    .push(view_term(r#type));

                                match term {
                                    None => entry.push(Text::new("")).push(Text::new("")),
                                    Some(term) => {
                                        entry.push(Text::new(" = ")).push(view_term(term))
                                    }
                                }
                            })
                        }),
                )
                .push(
                    TextInput::new(
                        input,
                        "Pikelet expression…",
                        input_value,
                        Message::InputChanged,
                    )
                    .on_submit(Message::InputSubmit),
                ),
        )
        .into()
    }
}

fn view_term<M: 'static>(term: &pikelet::lang::core::Term) -> Element<M> {
    use pikelet::lang::core::{Constant, Term, UniverseLevel, UniverseOffset};

    match term {
        Term::TypeType(UniverseLevel(level)) => Row::new()
            .push(Text::new(format!("Univ^{}", level))) // TODO: superscript?
            .into(),
        Term::Global(name) => Text::new(name).into(),
        Term::Local(_) => Text::new("todo").into(),
        Term::Constant(Constant::U8(data)) => Text::new(data.to_string()).into(),
        Term::Constant(Constant::U16(data)) => Text::new(data.to_string()).into(),
        Term::Constant(Constant::U32(data)) => Text::new(data.to_string()).into(),
        Term::Constant(Constant::U64(data)) => Text::new(data.to_string()).into(),
        Term::Constant(Constant::S8(data)) => Text::new(data.to_string()).into(),
        Term::Constant(Constant::S16(data)) => Text::new(data.to_string()).into(),
        Term::Constant(Constant::S32(data)) => Text::new(data.to_string()).into(),
        Term::Constant(Constant::S64(data)) => Text::new(data.to_string()).into(),
        Term::Constant(Constant::F32(data)) => Text::new(data.to_string()).into(),
        Term::Constant(Constant::F64(data)) => Text::new(data.to_string()).into(),
        Term::Constant(Constant::Char(data)) => Text::new(format!("{:?}", data)).into(),
        Term::Constant(Constant::String(data)) => Text::new(format!("{:?}", data)).into(),
        Term::Sequence(_) => Text::new("todo").into(),
        Term::Ann(term, r#type) => Row::new()
            .push(view_term(term))
            .push(Text::new(" : "))
            .push(view_term(r#type))
            .into(),
        Term::RecordTerm(_) => Text::new("todo").into(),
        Term::RecordType(_) => Text::new("todo").into(),
        Term::RecordElim(_, _) => Text::new("todo").into(),
        Term::FunctionType(_, _, _) => Text::new("todo").into(),
        Term::FunctionTerm(_, _) => Text::new("todo").into(),
        Term::FunctionElim(_, _) => Text::new("todo").into(),
        Term::Lift(term, UniverseOffset(offset)) => Row::new()
            .push(view_term(term))
            .push(Text::new(format!("^{}", offset)))
            .into(),
        Term::Error => Text::new("ERROR!").into(),
    }
}
