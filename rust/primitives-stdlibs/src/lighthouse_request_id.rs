use crate::lighthouse_request_id::beacon_node::lighthouse_network::service::Network;
use crate::lighthouse_request_id::beacon_node::network::service::NetworkService;
use std::marker::PhantomData;

pub mod beacon_node {
    pub mod network {
        pub mod service {
            use crate::lighthouse_request_id::beacon_node::lighthouse_network::service::Network;

            #[derive(Debug, Clone, Copy)]
            enum RequestId {
                Sync,
                Router,
            }

            pub struct NetworkService {
                libp2p: Network<RequestId>,
            }

            impl NetworkService {
                pub fn new() -> Self {
                    NetworkService {
                        libp2p: Network::new(),
                    }
                }

                pub fn on_network_msg(&self) {
                    self.libp2p.send_request(RequestId::Sync);
                }
            }
        }
    }

    pub mod lighthouse_network {
        mod rpc {
            use std::marker::PhantomData;

            pub trait ReqId: Send + 'static + std::fmt::Debug + Copy + Clone {}
            impl<T> ReqId for T where T: Send + 'static + std::fmt::Debug + Copy + Clone {}

            pub struct RPC<Id: ReqId> {
                phantom: PhantomData<Id>,
            }

            impl<Id: ReqId> RPC<Id> {
                pub fn new() -> Self {
                    RPC {
                        phantom: PhantomData::default(),
                    }
                }

                pub fn send_request(&self, _request_id: Id) {
                    println!("send_request");
                }
            }
        }

        pub mod api_type {
            #[derive(Debug, Clone, Copy, PartialEq, Eq)]
            pub enum RequestId<AppReqId> {
                Application(AppReqId),
                Internal,
            }
        }

        pub mod service {
            use crate::lighthouse_request_id::beacon_node::lighthouse_network::api_type::RequestId;
            use crate::lighthouse_request_id::beacon_node::lighthouse_network::rpc::{ReqId, RPC};
            use crate::lighthouse_request_id::beacon_node::lighthouse_network::service::behaviour::Behaviour;
            use crate::lighthouse_request_id::libp2p::Swarm;
            use std::marker::PhantomData;

            pub struct Network<AppReqId: ReqId> {
                swarm: Swarm<Behaviour<AppReqId>>,
            }

            impl<AppReqId: ReqId> Network<AppReqId> {
                pub fn new() -> Self {
                    Network {
                        swarm: Swarm::new(),
                    }
                }

                pub fn eth2_rpc_mut(&self) -> &RPC<RequestId<AppReqId>> {
                    &self.swarm.behaviour_mut().eth2_rpc
                }

                pub fn send_request(&self, request_id: AppReqId) {
                    self.eth2_rpc_mut()
                        .send_request(RequestId::Application(request_id));
                }
            }

            pub mod behaviour {
                use crate::lighthouse_request_id::beacon_node::lighthouse_network::api_type::RequestId;
                use crate::lighthouse_request_id::beacon_node::lighthouse_network::rpc::{
                    ReqId, RPC,
                };
                use crate::lighthouse_request_id::libp2p::NetworkBehaviour;

                pub struct Behaviour<AppReqId: ReqId> {
                    pub eth2_rpc: RPC<RequestId<AppReqId>>,
                }

                impl<AppReqId: ReqId> NetworkBehaviour for Behaviour<AppReqId> {
                    fn new() -> Self {
                        Behaviour {
                            eth2_rpc: RPC::new(),
                        }
                    }
                }
            }
        }
    }
}

pub mod libp2p {
    use crate::lighthouse_request_id::beacon_node::lighthouse_network::service::behaviour::Behaviour;
    use std::marker::PhantomData;

    pub struct Swarm<TBehaviour: NetworkBehaviour> {
        pub behaviour: TBehaviour,
    }

    impl<TBehaviour: NetworkBehaviour> Swarm<TBehaviour> {
        pub fn new() -> Self {
            Swarm {
                behaviour: TBehaviour::new(),
            }
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
    let service = NetworkService::new();
    service.on_network_msg();
}
