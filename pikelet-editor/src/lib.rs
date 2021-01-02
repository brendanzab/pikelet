use iced::{Column, Container, Element, Row, Sandbox, Settings, Text, TextInput};

pub fn run() -> Result<(), iced::Error> {
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
    use pikelet::lang::core::{Constant, TermData};

    match &term.data {
        TermData::Global(name) => Text::new(name).into(),
        TermData::Local(_) => Text::new("todo").into(),

        TermData::Ann(term, r#type) => Row::new()
            .push(view_term(term))
            .push(Text::new(" : "))
            .push(view_term(r#type))
            .into(),

        TermData::TypeType => Row::new().push(Text::new("Type")).into(),

        TermData::FunctionType(_, _, _) => Text::new("todo").into(),
        TermData::FunctionTerm(_, _) => Text::new("todo").into(),
        TermData::FunctionElim(_, _) => Text::new("todo").into(),

        TermData::RecordTerm(_) => Text::new("todo").into(),
        TermData::RecordType(_) => Text::new("todo").into(),
        TermData::RecordElim(_, _) => Text::new("todo").into(),

        TermData::EnumType(_) => Text::new("todo").into(),
        TermData::EnumTerm(_) => Text::new("todo").into(),
        TermData::EnumElim(_) => Text::new("todo").into(),

        TermData::ArrayTerm(_) => Text::new("todo").into(),
        TermData::ListTerm(_) => Text::new("todo").into(),

        TermData::Constant(Constant::U8(data)) => Text::new(data.to_string()).into(),
        TermData::Constant(Constant::U16(data)) => Text::new(data.to_string()).into(),
        TermData::Constant(Constant::U32(data)) => Text::new(data.to_string()).into(),
        TermData::Constant(Constant::U64(data)) => Text::new(data.to_string()).into(),
        TermData::Constant(Constant::S8(data)) => Text::new(data.to_string()).into(),
        TermData::Constant(Constant::S16(data)) => Text::new(data.to_string()).into(),
        TermData::Constant(Constant::S32(data)) => Text::new(data.to_string()).into(),
        TermData::Constant(Constant::S64(data)) => Text::new(data.to_string()).into(),
        TermData::Constant(Constant::F32(data)) => Text::new(data.to_string()).into(),
        TermData::Constant(Constant::F64(data)) => Text::new(data.to_string()).into(),
        TermData::Constant(Constant::Char(data)) => Text::new(format!("{:?}", data)).into(),
        TermData::Constant(Constant::String(data)) => Text::new(format!("{:?}", data)).into(),

        TermData::Error => Text::new("ERROR!").into(),
    }
}
