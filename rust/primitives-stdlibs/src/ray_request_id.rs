use crate::ray_request_id::network::{ApplicationRequestId, Network, NetworkMessage};

mod network {
    use crate::ray_request_id::behaviour::{BehaviourComposer, RequestId};
    use crate::ray_request_id::libp2p::NetworkBehaviour;
    use crate::ray_request_id::libp2p::Swarm;
    use std::marker::PhantomData;

    pub trait ReqId: Send + 'static + std::fmt::Debug + Copy + Clone {}
    impl<T> ReqId for T where T: Send + 'static + std::fmt::Debug + Copy + Clone {}

    pub(crate) struct Network<AppReqId: ReqId> {
        swarm: Swarm<BehaviourComposer<ApplicationRequestId>>,
        _phantom: PhantomData<AppReqId>,
    }

    impl<AppReqId: ReqId> Network<AppReqId> {
        pub(crate) fn new() -> Self {
            Network {
                swarm: Swarm::new(BehaviourComposer::new()),
                _phantom: Default::default(),
            }
        }

        pub(crate) fn on_network_message(&self, message: NetworkMessage) {
            match message {
                NetworkMessage::SendRequest { request_id } => {
                    self.send_request(request_id);
                }
            }
        }

        fn send_request(&self, request_id: ApplicationRequestId) {
            self.swarm
                .behaviour_mut()
                .rpc
                .send_request(RequestId::Application(request_id))
        }
    }

    #[derive(Debug, Clone, Copy)]
    pub(crate) enum ApplicationRequestId {
        Sync,
        Router,
    }

    pub(crate) enum NetworkMessage {
        SendRequest { request_id: ApplicationRequestId },
    }
}

mod rpc {
    pub(crate) mod behaviour {
        use crate::ray_request_id::network::ReqId;
        use std::marker::PhantomData;

        pub(crate) struct Behaviour<Id: ReqId> {
            _phantom: PhantomData<Id>,
        }

        impl<Id: ReqId> Behaviour<Id> {
            pub(crate) fn new() -> Self {
                Behaviour {
                    _phantom: Default::default(),
                }
            }

            pub(crate) fn send_request(&self, request_id: Id) {
                println!("send_request: {request_id:?}");
            }
        }
    }
}

pub(crate) mod behaviour {
    use crate::ray_request_id::libp2p::NetworkBehaviour;
    use crate::ray_request_id::network::ReqId;
    use crate::ray_request_id::rpc::behaviour::Behaviour;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum RequestId<AppReqId> {
        Application(AppReqId),
        Internal,
    }

    pub(crate) struct BehaviourComposer<AppReqId: ReqId> {
        pub(crate) rpc: Behaviour<RequestId<AppReqId>>,
    }

    impl<AppReqId: ReqId> NetworkBehaviour for BehaviourComposer<AppReqId> {
        fn new() -> Self {
            BehaviourComposer {
                rpc: Behaviour::new(),
            }
        }
    }
}

mod libp2p {
    pub struct Swarm<TBehaviour: NetworkBehaviour> {
        pub behaviour: TBehaviour,
    }

    impl<TBehaviour: NetworkBehaviour> Swarm<TBehaviour> {
        pub fn new(behaviour: TBehaviour) -> Self {
            Swarm { behaviour }
        }

        pub fn behaviour_mut(&self) -> &TBehaviour {
            &self.behaviour
        }
    }

    pub trait NetworkBehaviour {
        fn new() -> Self;
    }
}
#[test]
fn test() {
    let service: Network<ApplicationRequestId> = Network::new();
    service.on_network_message(NetworkMessage::SendRequest {
        request_id: ApplicationRequestId::Sync,
    });
}
