// This file is generated by rust-protobuf 2.22.0. Do not edit
// @generated

// https://github.com/rust-lang/rust-clippy/issues/702
#![allow(unknown_lints)]
#![allow(clippy::all)]

#![allow(unused_attributes)]
#![rustfmt::skip]

#![allow(box_pointers)]
#![allow(dead_code)]
#![allow(missing_docs)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(trivial_casts)]
#![allow(unused_imports)]
#![allow(unused_results)]
//! Generated file from `proto/tracing.proto`

/// Generated files are compatible only with the same version
/// of protobuf runtime.
// const _PROTOBUF_VERSION_CHECK: () = ::protobuf::VERSION_2_22_0;

#[derive(PartialEq,Clone,Default)]
pub struct Log {
    // message fields
    pub timestamp: ::protobuf::SingularPtrField<::protobuf::well_known_types::Timestamp>,
    // message oneof groups
    pub event: ::std::option::Option<Log_oneof_event>,
    // special fields
    pub unknown_fields: ::protobuf::UnknownFields,
    pub cached_size: ::protobuf::CachedSize,
}

impl<'a> ::std::default::Default for &'a Log {
    fn default() -> &'a Log {
        <Log as ::protobuf::Message>::default_instance()
    }
}

#[derive(Clone,PartialEq,Debug)]
pub enum Log_oneof_event {
    node_started(Log_NodeStarted),
    send_whoareyou(Log_SendWhoAreYou),
}

impl Log {
    pub fn new() -> Log {
        ::std::default::Default::default()
    }

    // .google.protobuf.Timestamp timestamp = 1;


    pub fn get_timestamp(&self) -> &::protobuf::well_known_types::Timestamp {
        self.timestamp.as_ref().unwrap_or_else(|| <::protobuf::well_known_types::Timestamp as ::protobuf::Message>::default_instance())
    }
    pub fn clear_timestamp(&mut self) {
        self.timestamp.clear();
    }

    pub fn has_timestamp(&self) -> bool {
        self.timestamp.is_some()
    }

    // Param is passed by value, moved
    pub fn set_timestamp(&mut self, v: ::protobuf::well_known_types::Timestamp) {
        self.timestamp = ::protobuf::SingularPtrField::some(v);
    }

    // Mutable pointer to the field.
    // If field is not initialized, it is initialized with default value first.
    pub fn mut_timestamp(&mut self) -> &mut ::protobuf::well_known_types::Timestamp {
        if self.timestamp.is_none() {
            self.timestamp.set_default();
        }
        self.timestamp.as_mut().unwrap()
    }

    // Take field
    pub fn take_timestamp(&mut self) -> ::protobuf::well_known_types::Timestamp {
        self.timestamp.take().unwrap_or_else(|| ::protobuf::well_known_types::Timestamp::new())
    }

    // .tracing.Log.NodeStarted node_started = 2;


    pub fn get_node_started(&self) -> &Log_NodeStarted {
        match self.event {
            ::std::option::Option::Some(Log_oneof_event::node_started(ref v)) => v,
            _ => <Log_NodeStarted as ::protobuf::Message>::default_instance(),
        }
    }
    pub fn clear_node_started(&mut self) {
        self.event = ::std::option::Option::None;
    }

    pub fn has_node_started(&self) -> bool {
        match self.event {
            ::std::option::Option::Some(Log_oneof_event::node_started(..)) => true,
            _ => false,
        }
    }

    // Param is passed by value, moved
    pub fn set_node_started(&mut self, v: Log_NodeStarted) {
        self.event = ::std::option::Option::Some(Log_oneof_event::node_started(v))
    }

    // Mutable pointer to the field.
    pub fn mut_node_started(&mut self) -> &mut Log_NodeStarted {
        if let ::std::option::Option::Some(Log_oneof_event::node_started(_)) = self.event {
        } else {
            self.event = ::std::option::Option::Some(Log_oneof_event::node_started(Log_NodeStarted::new()));
        }
        match self.event {
            ::std::option::Option::Some(Log_oneof_event::node_started(ref mut v)) => v,
            _ => panic!(),
        }
    }

    // Take field
    pub fn take_node_started(&mut self) -> Log_NodeStarted {
        if self.has_node_started() {
            match self.event.take() {
                ::std::option::Option::Some(Log_oneof_event::node_started(v)) => v,
                _ => panic!(),
            }
        } else {
            Log_NodeStarted::new()
        }
    }

    // .tracing.Log.SendWhoAreYou send_whoareyou = 3;


    pub fn get_send_whoareyou(&self) -> &Log_SendWhoAreYou {
        match self.event {
            ::std::option::Option::Some(Log_oneof_event::send_whoareyou(ref v)) => v,
            _ => <Log_SendWhoAreYou as ::protobuf::Message>::default_instance(),
        }
    }
    pub fn clear_send_whoareyou(&mut self) {
        self.event = ::std::option::Option::None;
    }

    pub fn has_send_whoareyou(&self) -> bool {
        match self.event {
            ::std::option::Option::Some(Log_oneof_event::send_whoareyou(..)) => true,
            _ => false,
        }
    }

    // Param is passed by value, moved
    pub fn set_send_whoareyou(&mut self, v: Log_SendWhoAreYou) {
        self.event = ::std::option::Option::Some(Log_oneof_event::send_whoareyou(v))
    }

    // Mutable pointer to the field.
    pub fn mut_send_whoareyou(&mut self) -> &mut Log_SendWhoAreYou {
        if let ::std::option::Option::Some(Log_oneof_event::send_whoareyou(_)) = self.event {
        } else {
            self.event = ::std::option::Option::Some(Log_oneof_event::send_whoareyou(Log_SendWhoAreYou::new()));
        }
        match self.event {
            ::std::option::Option::Some(Log_oneof_event::send_whoareyou(ref mut v)) => v,
            _ => panic!(),
        }
    }

    // Take field
    pub fn take_send_whoareyou(&mut self) -> Log_SendWhoAreYou {
        if self.has_send_whoareyou() {
            match self.event.take() {
                ::std::option::Option::Some(Log_oneof_event::send_whoareyou(v)) => v,
                _ => panic!(),
            }
        } else {
            Log_SendWhoAreYou::new()
        }
    }
}

impl ::protobuf::Message for Log {
    fn is_initialized(&self) -> bool {
        for v in &self.timestamp {
            if !v.is_initialized() {
                return false;
            }
        };
        if let Some(Log_oneof_event::node_started(ref v)) = self.event {
            if !v.is_initialized() {
                return false;
            }
        }
        if let Some(Log_oneof_event::send_whoareyou(ref v)) = self.event {
            if !v.is_initialized() {
                return false;
            }
        }
        true
    }

    fn merge_from(&mut self, is: &mut ::protobuf::CodedInputStream<'_>) -> ::protobuf::ProtobufResult<()> {
        while !is.eof()? {
            let (field_number, wire_type) = is.read_tag_unpack()?;
            match field_number {
                1 => {
                    ::protobuf::rt::read_singular_message_into(wire_type, is, &mut self.timestamp)?;
                },
                2 => {
                    if wire_type != ::protobuf::wire_format::WireTypeLengthDelimited {
                        return ::std::result::Result::Err(::protobuf::rt::unexpected_wire_type(wire_type));
                    }
                    self.event = ::std::option::Option::Some(Log_oneof_event::node_started(is.read_message()?));
                },
                3 => {
                    if wire_type != ::protobuf::wire_format::WireTypeLengthDelimited {
                        return ::std::result::Result::Err(::protobuf::rt::unexpected_wire_type(wire_type));
                    }
                    self.event = ::std::option::Option::Some(Log_oneof_event::send_whoareyou(is.read_message()?));
                },
                _ => {
                    ::protobuf::rt::read_unknown_or_skip_group(field_number, wire_type, is, self.mut_unknown_fields())?;
                },
            };
        }
        ::std::result::Result::Ok(())
    }

    // Compute sizes of nested messages
    #[allow(unused_variables)]
    fn compute_size(&self) -> u32 {
        let mut my_size = 0;
        if let Some(ref v) = self.timestamp.as_ref() {
            let len = v.compute_size();
            my_size += 1 + ::protobuf::rt::compute_raw_varint32_size(len) + len;
        }
        if let ::std::option::Option::Some(ref v) = self.event {
            match v {
                &Log_oneof_event::node_started(ref v) => {
                    let len = v.compute_size();
                    my_size += 1 + ::protobuf::rt::compute_raw_varint32_size(len) + len;
                },
                &Log_oneof_event::send_whoareyou(ref v) => {
                    let len = v.compute_size();
                    my_size += 1 + ::protobuf::rt::compute_raw_varint32_size(len) + len;
                },
            };
        }
        my_size += ::protobuf::rt::unknown_fields_size(self.get_unknown_fields());
        self.cached_size.set(my_size);
        my_size
    }

    fn write_to_with_cached_sizes(&self, os: &mut ::protobuf::CodedOutputStream<'_>) -> ::protobuf::ProtobufResult<()> {
        if let Some(ref v) = self.timestamp.as_ref() {
            os.write_tag(1, ::protobuf::wire_format::WireTypeLengthDelimited)?;
            os.write_raw_varint32(v.get_cached_size())?;
            v.write_to_with_cached_sizes(os)?;
        }
        if let ::std::option::Option::Some(ref v) = self.event {
            match v {
                &Log_oneof_event::node_started(ref v) => {
                    os.write_tag(2, ::protobuf::wire_format::WireTypeLengthDelimited)?;
                    os.write_raw_varint32(v.get_cached_size())?;
                    v.write_to_with_cached_sizes(os)?;
                },
                &Log_oneof_event::send_whoareyou(ref v) => {
                    os.write_tag(3, ::protobuf::wire_format::WireTypeLengthDelimited)?;
                    os.write_raw_varint32(v.get_cached_size())?;
                    v.write_to_with_cached_sizes(os)?;
                },
            };
        }
        os.write_unknown_fields(self.get_unknown_fields())?;
        ::std::result::Result::Ok(())
    }

    fn get_cached_size(&self) -> u32 {
        self.cached_size.get()
    }

    fn get_unknown_fields(&self) -> &::protobuf::UnknownFields {
        &self.unknown_fields
    }

    fn mut_unknown_fields(&mut self) -> &mut ::protobuf::UnknownFields {
        &mut self.unknown_fields
    }

    fn as_any(&self) -> &dyn (::std::any::Any) {
        self as &dyn (::std::any::Any)
    }
    fn as_any_mut(&mut self) -> &mut dyn (::std::any::Any) {
        self as &mut dyn (::std::any::Any)
    }
    fn into_any(self: ::std::boxed::Box<Self>) -> ::std::boxed::Box<dyn (::std::any::Any)> {
        self
    }

    fn descriptor(&self) -> &'static ::protobuf::reflect::MessageDescriptor {
        Self::descriptor_static()
    }

    fn new() -> Log {
        Log::new()
    }

    fn descriptor_static() -> &'static ::protobuf::reflect::MessageDescriptor {
        static descriptor: ::protobuf::rt::LazyV2<::protobuf::reflect::MessageDescriptor> = ::protobuf::rt::LazyV2::INIT;
        descriptor.get(|| {
            let mut fields = ::std::vec::Vec::new();
            fields.push(::protobuf::reflect::accessor::make_singular_ptr_field_accessor::<_, ::protobuf::types::ProtobufTypeMessage<::protobuf::well_known_types::Timestamp>>(
                "timestamp",
                |m: &Log| { &m.timestamp },
                |m: &mut Log| { &mut m.timestamp },
            ));
            fields.push(::protobuf::reflect::accessor::make_singular_message_accessor::<_, Log_NodeStarted>(
                "node_started",
                Log::has_node_started,
                Log::get_node_started,
            ));
            fields.push(::protobuf::reflect::accessor::make_singular_message_accessor::<_, Log_SendWhoAreYou>(
                "send_whoareyou",
                Log::has_send_whoareyou,
                Log::get_send_whoareyou,
            ));
            ::protobuf::reflect::MessageDescriptor::new_pb_name::<Log>(
                "Log",
                fields,
                file_descriptor_proto()
            )
        })
    }

    fn default_instance() -> &'static Log {
        static instance: ::protobuf::rt::LazyV2<Log> = ::protobuf::rt::LazyV2::INIT;
        instance.get(Log::new)
    }
}

impl ::protobuf::Clear for Log {
    fn clear(&mut self) {
        self.timestamp.clear();
        self.event = ::std::option::Option::None;
        self.event = ::std::option::Option::None;
        self.unknown_fields.clear();
    }
}

impl ::std::fmt::Debug for Log {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        ::protobuf::text_format::fmt(self, f)
    }
}

impl ::protobuf::reflect::ProtobufValue for Log {
    fn as_ref(&self) -> ::protobuf::reflect::ReflectValueRef {
        ::protobuf::reflect::ReflectValueRef::Message(self)
    }
}

#[derive(PartialEq,Clone,Default)]
pub struct Log_NodeStarted {
    // message fields
    pub node_id: ::std::string::String,
    // special fields
    pub unknown_fields: ::protobuf::UnknownFields,
    pub cached_size: ::protobuf::CachedSize,
}

impl<'a> ::std::default::Default for &'a Log_NodeStarted {
    fn default() -> &'a Log_NodeStarted {
        <Log_NodeStarted as ::protobuf::Message>::default_instance()
    }
}

impl Log_NodeStarted {
    pub fn new() -> Log_NodeStarted {
        ::std::default::Default::default()
    }

    // string node_id = 1;


    pub fn get_node_id(&self) -> &str {
        &self.node_id
    }
    pub fn clear_node_id(&mut self) {
        self.node_id.clear();
    }

    // Param is passed by value, moved
    pub fn set_node_id(&mut self, v: ::std::string::String) {
        self.node_id = v;
    }

    // Mutable pointer to the field.
    // If field is not initialized, it is initialized with default value first.
    pub fn mut_node_id(&mut self) -> &mut ::std::string::String {
        &mut self.node_id
    }

    // Take field
    pub fn take_node_id(&mut self) -> ::std::string::String {
        ::std::mem::replace(&mut self.node_id, ::std::string::String::new())
    }
}

impl ::protobuf::Message for Log_NodeStarted {
    fn is_initialized(&self) -> bool {
        true
    }

    fn merge_from(&mut self, is: &mut ::protobuf::CodedInputStream<'_>) -> ::protobuf::ProtobufResult<()> {
        while !is.eof()? {
            let (field_number, wire_type) = is.read_tag_unpack()?;
            match field_number {
                1 => {
                    ::protobuf::rt::read_singular_proto3_string_into(wire_type, is, &mut self.node_id)?;
                },
                _ => {
                    ::protobuf::rt::read_unknown_or_skip_group(field_number, wire_type, is, self.mut_unknown_fields())?;
                },
            };
        }
        ::std::result::Result::Ok(())
    }

    // Compute sizes of nested messages
    #[allow(unused_variables)]
    fn compute_size(&self) -> u32 {
        let mut my_size = 0;
        if !self.node_id.is_empty() {
            my_size += ::protobuf::rt::string_size(1, &self.node_id);
        }
        my_size += ::protobuf::rt::unknown_fields_size(self.get_unknown_fields());
        self.cached_size.set(my_size);
        my_size
    }

    fn write_to_with_cached_sizes(&self, os: &mut ::protobuf::CodedOutputStream<'_>) -> ::protobuf::ProtobufResult<()> {
        if !self.node_id.is_empty() {
            os.write_string(1, &self.node_id)?;
        }
        os.write_unknown_fields(self.get_unknown_fields())?;
        ::std::result::Result::Ok(())
    }

    fn get_cached_size(&self) -> u32 {
        self.cached_size.get()
    }

    fn get_unknown_fields(&self) -> &::protobuf::UnknownFields {
        &self.unknown_fields
    }

    fn mut_unknown_fields(&mut self) -> &mut ::protobuf::UnknownFields {
        &mut self.unknown_fields
    }

    fn as_any(&self) -> &dyn (::std::any::Any) {
        self as &dyn (::std::any::Any)
    }
    fn as_any_mut(&mut self) -> &mut dyn (::std::any::Any) {
        self as &mut dyn (::std::any::Any)
    }
    fn into_any(self: ::std::boxed::Box<Self>) -> ::std::boxed::Box<dyn (::std::any::Any)> {
        self
    }

    fn descriptor(&self) -> &'static ::protobuf::reflect::MessageDescriptor {
        Self::descriptor_static()
    }

    fn new() -> Log_NodeStarted {
        Log_NodeStarted::new()
    }

    fn descriptor_static() -> &'static ::protobuf::reflect::MessageDescriptor {
        static descriptor: ::protobuf::rt::LazyV2<::protobuf::reflect::MessageDescriptor> = ::protobuf::rt::LazyV2::INIT;
        descriptor.get(|| {
            let mut fields = ::std::vec::Vec::new();
            fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeString>(
                "node_id",
                |m: &Log_NodeStarted| { &m.node_id },
                |m: &mut Log_NodeStarted| { &mut m.node_id },
            ));
            ::protobuf::reflect::MessageDescriptor::new_pb_name::<Log_NodeStarted>(
                "Log.NodeStarted",
                fields,
                file_descriptor_proto()
            )
        })
    }

    fn default_instance() -> &'static Log_NodeStarted {
        static instance: ::protobuf::rt::LazyV2<Log_NodeStarted> = ::protobuf::rt::LazyV2::INIT;
        instance.get(Log_NodeStarted::new)
    }
}

impl ::protobuf::Clear for Log_NodeStarted {
    fn clear(&mut self) {
        self.node_id.clear();
        self.unknown_fields.clear();
    }
}

impl ::std::fmt::Debug for Log_NodeStarted {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        ::protobuf::text_format::fmt(self, f)
    }
}

impl ::protobuf::reflect::ProtobufValue for Log_NodeStarted {
    fn as_ref(&self) -> ::protobuf::reflect::ReflectValueRef {
        ::protobuf::reflect::ReflectValueRef::Message(self)
    }
}

#[derive(PartialEq,Clone,Default)]
pub struct Log_SendWhoAreYou {
    // message fields
    pub sender: ::std::string::String,
    pub recipient: ::std::string::String,
    pub id_nonce: u64,
    pub enr_seq: u64,
    // special fields
    pub unknown_fields: ::protobuf::UnknownFields,
    pub cached_size: ::protobuf::CachedSize,
}

impl<'a> ::std::default::Default for &'a Log_SendWhoAreYou {
    fn default() -> &'a Log_SendWhoAreYou {
        <Log_SendWhoAreYou as ::protobuf::Message>::default_instance()
    }
}

impl Log_SendWhoAreYou {
    pub fn new() -> Log_SendWhoAreYou {
        ::std::default::Default::default()
    }

    // string sender = 1;


    pub fn get_sender(&self) -> &str {
        &self.sender
    }
    pub fn clear_sender(&mut self) {
        self.sender.clear();
    }

    // Param is passed by value, moved
    pub fn set_sender(&mut self, v: ::std::string::String) {
        self.sender = v;
    }

    // Mutable pointer to the field.
    // If field is not initialized, it is initialized with default value first.
    pub fn mut_sender(&mut self) -> &mut ::std::string::String {
        &mut self.sender
    }

    // Take field
    pub fn take_sender(&mut self) -> ::std::string::String {
        ::std::mem::replace(&mut self.sender, ::std::string::String::new())
    }

    // string recipient = 2;


    pub fn get_recipient(&self) -> &str {
        &self.recipient
    }
    pub fn clear_recipient(&mut self) {
        self.recipient.clear();
    }

    // Param is passed by value, moved
    pub fn set_recipient(&mut self, v: ::std::string::String) {
        self.recipient = v;
    }

    // Mutable pointer to the field.
    // If field is not initialized, it is initialized with default value first.
    pub fn mut_recipient(&mut self) -> &mut ::std::string::String {
        &mut self.recipient
    }

    // Take field
    pub fn take_recipient(&mut self) -> ::std::string::String {
        ::std::mem::replace(&mut self.recipient, ::std::string::String::new())
    }

    // uint64 id_nonce = 3;


    pub fn get_id_nonce(&self) -> u64 {
        self.id_nonce
    }
    pub fn clear_id_nonce(&mut self) {
        self.id_nonce = 0;
    }

    // Param is passed by value, moved
    pub fn set_id_nonce(&mut self, v: u64) {
        self.id_nonce = v;
    }

    // uint64 enr_seq = 4;


    pub fn get_enr_seq(&self) -> u64 {
        self.enr_seq
    }
    pub fn clear_enr_seq(&mut self) {
        self.enr_seq = 0;
    }

    // Param is passed by value, moved
    pub fn set_enr_seq(&mut self, v: u64) {
        self.enr_seq = v;
    }
}

impl ::protobuf::Message for Log_SendWhoAreYou {
    fn is_initialized(&self) -> bool {
        true
    }

    fn merge_from(&mut self, is: &mut ::protobuf::CodedInputStream<'_>) -> ::protobuf::ProtobufResult<()> {
        while !is.eof()? {
            let (field_number, wire_type) = is.read_tag_unpack()?;
            match field_number {
                1 => {
                    ::protobuf::rt::read_singular_proto3_string_into(wire_type, is, &mut self.sender)?;
                },
                2 => {
                    ::protobuf::rt::read_singular_proto3_string_into(wire_type, is, &mut self.recipient)?;
                },
                3 => {
                    if wire_type != ::protobuf::wire_format::WireTypeVarint {
                        return ::std::result::Result::Err(::protobuf::rt::unexpected_wire_type(wire_type));
                    }
                    let tmp = is.read_uint64()?;
                    self.id_nonce = tmp;
                },
                4 => {
                    if wire_type != ::protobuf::wire_format::WireTypeVarint {
                        return ::std::result::Result::Err(::protobuf::rt::unexpected_wire_type(wire_type));
                    }
                    let tmp = is.read_uint64()?;
                    self.enr_seq = tmp;
                },
                _ => {
                    ::protobuf::rt::read_unknown_or_skip_group(field_number, wire_type, is, self.mut_unknown_fields())?;
                },
            };
        }
        ::std::result::Result::Ok(())
    }

    // Compute sizes of nested messages
    #[allow(unused_variables)]
    fn compute_size(&self) -> u32 {
        let mut my_size = 0;
        if !self.sender.is_empty() {
            my_size += ::protobuf::rt::string_size(1, &self.sender);
        }
        if !self.recipient.is_empty() {
            my_size += ::protobuf::rt::string_size(2, &self.recipient);
        }
        if self.id_nonce != 0 {
            my_size += ::protobuf::rt::value_size(3, self.id_nonce, ::protobuf::wire_format::WireTypeVarint);
        }
        if self.enr_seq != 0 {
            my_size += ::protobuf::rt::value_size(4, self.enr_seq, ::protobuf::wire_format::WireTypeVarint);
        }
        my_size += ::protobuf::rt::unknown_fields_size(self.get_unknown_fields());
        self.cached_size.set(my_size);
        my_size
    }

    fn write_to_with_cached_sizes(&self, os: &mut ::protobuf::CodedOutputStream<'_>) -> ::protobuf::ProtobufResult<()> {
        if !self.sender.is_empty() {
            os.write_string(1, &self.sender)?;
        }
        if !self.recipient.is_empty() {
            os.write_string(2, &self.recipient)?;
        }
        if self.id_nonce != 0 {
            os.write_uint64(3, self.id_nonce)?;
        }
        if self.enr_seq != 0 {
            os.write_uint64(4, self.enr_seq)?;
        }
        os.write_unknown_fields(self.get_unknown_fields())?;
        ::std::result::Result::Ok(())
    }

    fn get_cached_size(&self) -> u32 {
        self.cached_size.get()
    }

    fn get_unknown_fields(&self) -> &::protobuf::UnknownFields {
        &self.unknown_fields
    }

    fn mut_unknown_fields(&mut self) -> &mut ::protobuf::UnknownFields {
        &mut self.unknown_fields
    }

    fn as_any(&self) -> &dyn (::std::any::Any) {
        self as &dyn (::std::any::Any)
    }
    fn as_any_mut(&mut self) -> &mut dyn (::std::any::Any) {
        self as &mut dyn (::std::any::Any)
    }
    fn into_any(self: ::std::boxed::Box<Self>) -> ::std::boxed::Box<dyn (::std::any::Any)> {
        self
    }

    fn descriptor(&self) -> &'static ::protobuf::reflect::MessageDescriptor {
        Self::descriptor_static()
    }

    fn new() -> Log_SendWhoAreYou {
        Log_SendWhoAreYou::new()
    }

    fn descriptor_static() -> &'static ::protobuf::reflect::MessageDescriptor {
        static descriptor: ::protobuf::rt::LazyV2<::protobuf::reflect::MessageDescriptor> = ::protobuf::rt::LazyV2::INIT;
        descriptor.get(|| {
            let mut fields = ::std::vec::Vec::new();
            fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeString>(
                "sender",
                |m: &Log_SendWhoAreYou| { &m.sender },
                |m: &mut Log_SendWhoAreYou| { &mut m.sender },
            ));
            fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeString>(
                "recipient",
                |m: &Log_SendWhoAreYou| { &m.recipient },
                |m: &mut Log_SendWhoAreYou| { &mut m.recipient },
            ));
            fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeUint64>(
                "id_nonce",
                |m: &Log_SendWhoAreYou| { &m.id_nonce },
                |m: &mut Log_SendWhoAreYou| { &mut m.id_nonce },
            ));
            fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeUint64>(
                "enr_seq",
                |m: &Log_SendWhoAreYou| { &m.enr_seq },
                |m: &mut Log_SendWhoAreYou| { &mut m.enr_seq },
            ));
            ::protobuf::reflect::MessageDescriptor::new_pb_name::<Log_SendWhoAreYou>(
                "Log.SendWhoAreYou",
                fields,
                file_descriptor_proto()
            )
        })
    }

    fn default_instance() -> &'static Log_SendWhoAreYou {
        static instance: ::protobuf::rt::LazyV2<Log_SendWhoAreYou> = ::protobuf::rt::LazyV2::INIT;
        instance.get(Log_SendWhoAreYou::new)
    }
}

impl ::protobuf::Clear for Log_SendWhoAreYou {
    fn clear(&mut self) {
        self.sender.clear();
        self.recipient.clear();
        self.id_nonce = 0;
        self.enr_seq = 0;
        self.unknown_fields.clear();
    }
}

impl ::std::fmt::Debug for Log_SendWhoAreYou {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        ::protobuf::text_format::fmt(self, f)
    }
}

impl ::protobuf::reflect::ProtobufValue for Log_SendWhoAreYou {
    fn as_ref(&self) -> ::protobuf::reflect::ReflectValueRef {
        ::protobuf::reflect::ReflectValueRef::Message(self)
    }
}

static file_descriptor_proto_data: &'static [u8] = b"\
    \n\x13proto/tracing.proto\x12\x07tracing\x1a\x1fgoogle/protobuf/timestam\
    p.proto\"\xef\x02\n\x03Log\x128\n\ttimestamp\x18\x01\x20\x01(\x0b2\x1a.g\
    oogle.protobuf.TimestampR\ttimestamp\x12=\n\x0cnode_started\x18\x02\x20\
    \x01(\x0b2\x18.tracing.Log.NodeStartedH\0R\x0bnodeStarted\x12C\n\x0esend\
    _whoareyou\x18\x03\x20\x01(\x0b2\x1a.tracing.Log.SendWhoAreYouH\0R\rsend\
    Whoareyou\x1a&\n\x0bNodeStarted\x12\x17\n\x07node_id\x18\x01\x20\x01(\tR\
    \x06nodeId\x1ay\n\rSendWhoAreYou\x12\x16\n\x06sender\x18\x01\x20\x01(\tR\
    \x06sender\x12\x1c\n\trecipient\x18\x02\x20\x01(\tR\trecipient\x12\x19\n\
    \x08id_nonce\x18\x03\x20\x01(\x04R\x07idNonce\x12\x17\n\x07enr_seq\x18\
    \x04\x20\x01(\x04R\x06enrSeqB\x07\n\x05eventb\x06proto3\
";

static file_descriptor_proto_lazy: ::protobuf::rt::LazyV2<::protobuf::descriptor::FileDescriptorProto> = ::protobuf::rt::LazyV2::INIT;

fn parse_descriptor_proto() -> ::protobuf::descriptor::FileDescriptorProto {
    ::protobuf::Message::parse_from_bytes(file_descriptor_proto_data).unwrap()
}

pub fn file_descriptor_proto() -> &'static ::protobuf::descriptor::FileDescriptorProto {
    file_descriptor_proto_lazy.get(|| {
        parse_descriptor_proto()
    })
}
