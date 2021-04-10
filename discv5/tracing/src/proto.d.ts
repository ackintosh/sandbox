import * as $protobuf from "protobufjs";
/** Namespace tracing. */
export namespace tracing {

    /** Properties of a Log. */
    interface ILog {

        /** Log timestamp */
        timestamp?: (google.protobuf.ITimestamp|null);

        /** Log start */
        start?: (tracing.Log.IStart|null);

        /** Log shutdown */
        shutdown?: (tracing.Log.IShutdown|null);

        /** Log sendWhoareyou */
        sendWhoareyou?: (tracing.Log.ISendWhoAreYou|null);

        /** Log sendOrdinaryMessage */
        sendOrdinaryMessage?: (tracing.Log.ISendOrdinaryMessage|null);

        /** Log handleOrdinaryMessage */
        handleOrdinaryMessage?: (tracing.Log.IHandleOrdinaryMessage|null);

        /** Log sendHandshakeMessage */
        sendHandshakeMessage?: (tracing.Log.ISendHandshakeMessage|null);
    }

    /** Represents a Log. */
    class Log implements ILog {

        /**
         * Constructs a new Log.
         * @param [properties] Properties to set
         */
        constructor(properties?: tracing.ILog);

        /** Log timestamp. */
        public timestamp?: (google.protobuf.ITimestamp|null);

        /** Log start. */
        public start?: (tracing.Log.IStart|null);

        /** Log shutdown. */
        public shutdown?: (tracing.Log.IShutdown|null);

        /** Log sendWhoareyou. */
        public sendWhoareyou?: (tracing.Log.ISendWhoAreYou|null);

        /** Log sendOrdinaryMessage. */
        public sendOrdinaryMessage?: (tracing.Log.ISendOrdinaryMessage|null);

        /** Log handleOrdinaryMessage. */
        public handleOrdinaryMessage?: (tracing.Log.IHandleOrdinaryMessage|null);

        /** Log sendHandshakeMessage. */
        public sendHandshakeMessage?: (tracing.Log.ISendHandshakeMessage|null);

        /** Log event. */
        public event?: ("start"|"shutdown"|"sendWhoareyou"|"sendOrdinaryMessage"|"handleOrdinaryMessage"|"sendHandshakeMessage");

        /**
         * Creates a new Log instance using the specified properties.
         * @param [properties] Properties to set
         * @returns Log instance
         */
        public static create(properties?: tracing.ILog): tracing.Log;

        /**
         * Encodes the specified Log message. Does not implicitly {@link tracing.Log.verify|verify} messages.
         * @param message Log message or plain object to encode
         * @param [writer] Writer to encode to
         * @returns Writer
         */
        public static encode(message: tracing.ILog, writer?: $protobuf.Writer): $protobuf.Writer;

        /**
         * Encodes the specified Log message, length delimited. Does not implicitly {@link tracing.Log.verify|verify} messages.
         * @param message Log message or plain object to encode
         * @param [writer] Writer to encode to
         * @returns Writer
         */
        public static encodeDelimited(message: tracing.ILog, writer?: $protobuf.Writer): $protobuf.Writer;

        /**
         * Decodes a Log message from the specified reader or buffer.
         * @param reader Reader or buffer to decode from
         * @param [length] Message length if known beforehand
         * @returns Log
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.Log;

        /**
         * Decodes a Log message from the specified reader or buffer, length delimited.
         * @param reader Reader or buffer to decode from
         * @returns Log
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.Log;

        /**
         * Verifies a Log message.
         * @param message Plain object to verify
         * @returns `null` if valid, otherwise the reason why it is not
         */
        public static verify(message: { [k: string]: any }): (string|null);

        /**
         * Creates a Log message from a plain object. Also converts values to their respective internal types.
         * @param object Plain object
         * @returns Log
         */
        public static fromObject(object: { [k: string]: any }): tracing.Log;

        /**
         * Creates a plain object from a Log message. Also converts values to other types if specified.
         * @param message Log
         * @param [options] Conversion options
         * @returns Plain object
         */
        public static toObject(message: tracing.Log, options?: $protobuf.IConversionOptions): { [k: string]: any };

        /**
         * Converts this Log to JSON.
         * @returns JSON object
         */
        public toJSON(): { [k: string]: any };
    }

    namespace Log {

        /** Properties of a Start. */
        interface IStart {

            /** Start nodeId */
            nodeId?: (string|null);
        }

        /** Represents a Start. */
        class Start implements IStart {

            /**
             * Constructs a new Start.
             * @param [properties] Properties to set
             */
            constructor(properties?: tracing.Log.IStart);

            /** Start nodeId. */
            public nodeId: string;

            /**
             * Creates a new Start instance using the specified properties.
             * @param [properties] Properties to set
             * @returns Start instance
             */
            public static create(properties?: tracing.Log.IStart): tracing.Log.Start;

            /**
             * Encodes the specified Start message. Does not implicitly {@link tracing.Log.Start.verify|verify} messages.
             * @param message Start message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encode(message: tracing.Log.IStart, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Encodes the specified Start message, length delimited. Does not implicitly {@link tracing.Log.Start.verify|verify} messages.
             * @param message Start message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encodeDelimited(message: tracing.Log.IStart, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Decodes a Start message from the specified reader or buffer.
             * @param reader Reader or buffer to decode from
             * @param [length] Message length if known beforehand
             * @returns Start
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.Log.Start;

            /**
             * Decodes a Start message from the specified reader or buffer, length delimited.
             * @param reader Reader or buffer to decode from
             * @returns Start
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.Log.Start;

            /**
             * Verifies a Start message.
             * @param message Plain object to verify
             * @returns `null` if valid, otherwise the reason why it is not
             */
            public static verify(message: { [k: string]: any }): (string|null);

            /**
             * Creates a Start message from a plain object. Also converts values to their respective internal types.
             * @param object Plain object
             * @returns Start
             */
            public static fromObject(object: { [k: string]: any }): tracing.Log.Start;

            /**
             * Creates a plain object from a Start message. Also converts values to other types if specified.
             * @param message Start
             * @param [options] Conversion options
             * @returns Plain object
             */
            public static toObject(message: tracing.Log.Start, options?: $protobuf.IConversionOptions): { [k: string]: any };

            /**
             * Converts this Start to JSON.
             * @returns JSON object
             */
            public toJSON(): { [k: string]: any };
        }

        /** Properties of a Shutdown. */
        interface IShutdown {

            /** Shutdown nodeId */
            nodeId?: (string|null);
        }

        /** Represents a Shutdown. */
        class Shutdown implements IShutdown {

            /**
             * Constructs a new Shutdown.
             * @param [properties] Properties to set
             */
            constructor(properties?: tracing.Log.IShutdown);

            /** Shutdown nodeId. */
            public nodeId: string;

            /**
             * Creates a new Shutdown instance using the specified properties.
             * @param [properties] Properties to set
             * @returns Shutdown instance
             */
            public static create(properties?: tracing.Log.IShutdown): tracing.Log.Shutdown;

            /**
             * Encodes the specified Shutdown message. Does not implicitly {@link tracing.Log.Shutdown.verify|verify} messages.
             * @param message Shutdown message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encode(message: tracing.Log.IShutdown, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Encodes the specified Shutdown message, length delimited. Does not implicitly {@link tracing.Log.Shutdown.verify|verify} messages.
             * @param message Shutdown message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encodeDelimited(message: tracing.Log.IShutdown, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Decodes a Shutdown message from the specified reader or buffer.
             * @param reader Reader or buffer to decode from
             * @param [length] Message length if known beforehand
             * @returns Shutdown
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.Log.Shutdown;

            /**
             * Decodes a Shutdown message from the specified reader or buffer, length delimited.
             * @param reader Reader or buffer to decode from
             * @returns Shutdown
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.Log.Shutdown;

            /**
             * Verifies a Shutdown message.
             * @param message Plain object to verify
             * @returns `null` if valid, otherwise the reason why it is not
             */
            public static verify(message: { [k: string]: any }): (string|null);

            /**
             * Creates a Shutdown message from a plain object. Also converts values to their respective internal types.
             * @param object Plain object
             * @returns Shutdown
             */
            public static fromObject(object: { [k: string]: any }): tracing.Log.Shutdown;

            /**
             * Creates a plain object from a Shutdown message. Also converts values to other types if specified.
             * @param message Shutdown
             * @param [options] Conversion options
             * @returns Plain object
             */
            public static toObject(message: tracing.Log.Shutdown, options?: $protobuf.IConversionOptions): { [k: string]: any };

            /**
             * Converts this Shutdown to JSON.
             * @returns JSON object
             */
            public toJSON(): { [k: string]: any };
        }

        /** Properties of a SendWhoAreYou. */
        interface ISendWhoAreYou {

            /** SendWhoAreYou sender */
            sender?: (string|null);

            /** SendWhoAreYou recipient */
            recipient?: (string|null);

            /** SendWhoAreYou idNonce */
            idNonce?: (number[]|null);

            /** SendWhoAreYou enrSeq */
            enrSeq?: (number|Long|null);
        }

        /** Represents a SendWhoAreYou. */
        class SendWhoAreYou implements ISendWhoAreYou {

            /**
             * Constructs a new SendWhoAreYou.
             * @param [properties] Properties to set
             */
            constructor(properties?: tracing.Log.ISendWhoAreYou);

            /** SendWhoAreYou sender. */
            public sender: string;

            /** SendWhoAreYou recipient. */
            public recipient: string;

            /** SendWhoAreYou idNonce. */
            public idNonce: number[];

            /** SendWhoAreYou enrSeq. */
            public enrSeq: (number|Long);

            /**
             * Creates a new SendWhoAreYou instance using the specified properties.
             * @param [properties] Properties to set
             * @returns SendWhoAreYou instance
             */
            public static create(properties?: tracing.Log.ISendWhoAreYou): tracing.Log.SendWhoAreYou;

            /**
             * Encodes the specified SendWhoAreYou message. Does not implicitly {@link tracing.Log.SendWhoAreYou.verify|verify} messages.
             * @param message SendWhoAreYou message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encode(message: tracing.Log.ISendWhoAreYou, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Encodes the specified SendWhoAreYou message, length delimited. Does not implicitly {@link tracing.Log.SendWhoAreYou.verify|verify} messages.
             * @param message SendWhoAreYou message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encodeDelimited(message: tracing.Log.ISendWhoAreYou, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Decodes a SendWhoAreYou message from the specified reader or buffer.
             * @param reader Reader or buffer to decode from
             * @param [length] Message length if known beforehand
             * @returns SendWhoAreYou
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.Log.SendWhoAreYou;

            /**
             * Decodes a SendWhoAreYou message from the specified reader or buffer, length delimited.
             * @param reader Reader or buffer to decode from
             * @returns SendWhoAreYou
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.Log.SendWhoAreYou;

            /**
             * Verifies a SendWhoAreYou message.
             * @param message Plain object to verify
             * @returns `null` if valid, otherwise the reason why it is not
             */
            public static verify(message: { [k: string]: any }): (string|null);

            /**
             * Creates a SendWhoAreYou message from a plain object. Also converts values to their respective internal types.
             * @param object Plain object
             * @returns SendWhoAreYou
             */
            public static fromObject(object: { [k: string]: any }): tracing.Log.SendWhoAreYou;

            /**
             * Creates a plain object from a SendWhoAreYou message. Also converts values to other types if specified.
             * @param message SendWhoAreYou
             * @param [options] Conversion options
             * @returns Plain object
             */
            public static toObject(message: tracing.Log.SendWhoAreYou, options?: $protobuf.IConversionOptions): { [k: string]: any };

            /**
             * Converts this SendWhoAreYou to JSON.
             * @returns JSON object
             */
            public toJSON(): { [k: string]: any };
        }

        /** Properties of a SendOrdinaryMessage. */
        interface ISendOrdinaryMessage {

            /** SendOrdinaryMessage sender */
            sender?: (string|null);

            /** SendOrdinaryMessage recipient */
            recipient?: (string|null);

            /** SendOrdinaryMessage random */
            random?: (tracing.IRandom|null);

            /** SendOrdinaryMessage ping */
            ping?: (tracing.IPing|null);

            /** SendOrdinaryMessage pong */
            pong?: (tracing.IPong|null);

            /** SendOrdinaryMessage findNode */
            findNode?: (tracing.IFindNode|null);

            /** SendOrdinaryMessage nodes */
            nodes?: (tracing.INodes|null);
        }

        /** Represents a SendOrdinaryMessage. */
        class SendOrdinaryMessage implements ISendOrdinaryMessage {

            /**
             * Constructs a new SendOrdinaryMessage.
             * @param [properties] Properties to set
             */
            constructor(properties?: tracing.Log.ISendOrdinaryMessage);

            /** SendOrdinaryMessage sender. */
            public sender: string;

            /** SendOrdinaryMessage recipient. */
            public recipient: string;

            /** SendOrdinaryMessage random. */
            public random?: (tracing.IRandom|null);

            /** SendOrdinaryMessage ping. */
            public ping?: (tracing.IPing|null);

            /** SendOrdinaryMessage pong. */
            public pong?: (tracing.IPong|null);

            /** SendOrdinaryMessage findNode. */
            public findNode?: (tracing.IFindNode|null);

            /** SendOrdinaryMessage nodes. */
            public nodes?: (tracing.INodes|null);

            /** SendOrdinaryMessage message. */
            public message?: ("random"|"ping"|"pong"|"findNode"|"nodes");

            /**
             * Creates a new SendOrdinaryMessage instance using the specified properties.
             * @param [properties] Properties to set
             * @returns SendOrdinaryMessage instance
             */
            public static create(properties?: tracing.Log.ISendOrdinaryMessage): tracing.Log.SendOrdinaryMessage;

            /**
             * Encodes the specified SendOrdinaryMessage message. Does not implicitly {@link tracing.Log.SendOrdinaryMessage.verify|verify} messages.
             * @param message SendOrdinaryMessage message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encode(message: tracing.Log.ISendOrdinaryMessage, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Encodes the specified SendOrdinaryMessage message, length delimited. Does not implicitly {@link tracing.Log.SendOrdinaryMessage.verify|verify} messages.
             * @param message SendOrdinaryMessage message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encodeDelimited(message: tracing.Log.ISendOrdinaryMessage, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Decodes a SendOrdinaryMessage message from the specified reader or buffer.
             * @param reader Reader or buffer to decode from
             * @param [length] Message length if known beforehand
             * @returns SendOrdinaryMessage
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.Log.SendOrdinaryMessage;

            /**
             * Decodes a SendOrdinaryMessage message from the specified reader or buffer, length delimited.
             * @param reader Reader or buffer to decode from
             * @returns SendOrdinaryMessage
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.Log.SendOrdinaryMessage;

            /**
             * Verifies a SendOrdinaryMessage message.
             * @param message Plain object to verify
             * @returns `null` if valid, otherwise the reason why it is not
             */
            public static verify(message: { [k: string]: any }): (string|null);

            /**
             * Creates a SendOrdinaryMessage message from a plain object. Also converts values to their respective internal types.
             * @param object Plain object
             * @returns SendOrdinaryMessage
             */
            public static fromObject(object: { [k: string]: any }): tracing.Log.SendOrdinaryMessage;

            /**
             * Creates a plain object from a SendOrdinaryMessage message. Also converts values to other types if specified.
             * @param message SendOrdinaryMessage
             * @param [options] Conversion options
             * @returns Plain object
             */
            public static toObject(message: tracing.Log.SendOrdinaryMessage, options?: $protobuf.IConversionOptions): { [k: string]: any };

            /**
             * Converts this SendOrdinaryMessage to JSON.
             * @returns JSON object
             */
            public toJSON(): { [k: string]: any };
        }

        /** Properties of a HandleOrdinaryMessage. */
        interface IHandleOrdinaryMessage {

            /** HandleOrdinaryMessage sender */
            sender?: (string|null);

            /** HandleOrdinaryMessage recipient */
            recipient?: (string|null);

            /** HandleOrdinaryMessage random */
            random?: (tracing.IRandom|null);

            /** HandleOrdinaryMessage ping */
            ping?: (tracing.IPing|null);

            /** HandleOrdinaryMessage pong */
            pong?: (tracing.IPong|null);

            /** HandleOrdinaryMessage findNode */
            findNode?: (tracing.IFindNode|null);

            /** HandleOrdinaryMessage nodes */
            nodes?: (tracing.INodes|null);
        }

        /** Represents a HandleOrdinaryMessage. */
        class HandleOrdinaryMessage implements IHandleOrdinaryMessage {

            /**
             * Constructs a new HandleOrdinaryMessage.
             * @param [properties] Properties to set
             */
            constructor(properties?: tracing.Log.IHandleOrdinaryMessage);

            /** HandleOrdinaryMessage sender. */
            public sender: string;

            /** HandleOrdinaryMessage recipient. */
            public recipient: string;

            /** HandleOrdinaryMessage random. */
            public random?: (tracing.IRandom|null);

            /** HandleOrdinaryMessage ping. */
            public ping?: (tracing.IPing|null);

            /** HandleOrdinaryMessage pong. */
            public pong?: (tracing.IPong|null);

            /** HandleOrdinaryMessage findNode. */
            public findNode?: (tracing.IFindNode|null);

            /** HandleOrdinaryMessage nodes. */
            public nodes?: (tracing.INodes|null);

            /** HandleOrdinaryMessage message. */
            public message?: ("random"|"ping"|"pong"|"findNode"|"nodes");

            /**
             * Creates a new HandleOrdinaryMessage instance using the specified properties.
             * @param [properties] Properties to set
             * @returns HandleOrdinaryMessage instance
             */
            public static create(properties?: tracing.Log.IHandleOrdinaryMessage): tracing.Log.HandleOrdinaryMessage;

            /**
             * Encodes the specified HandleOrdinaryMessage message. Does not implicitly {@link tracing.Log.HandleOrdinaryMessage.verify|verify} messages.
             * @param message HandleOrdinaryMessage message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encode(message: tracing.Log.IHandleOrdinaryMessage, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Encodes the specified HandleOrdinaryMessage message, length delimited. Does not implicitly {@link tracing.Log.HandleOrdinaryMessage.verify|verify} messages.
             * @param message HandleOrdinaryMessage message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encodeDelimited(message: tracing.Log.IHandleOrdinaryMessage, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Decodes a HandleOrdinaryMessage message from the specified reader or buffer.
             * @param reader Reader or buffer to decode from
             * @param [length] Message length if known beforehand
             * @returns HandleOrdinaryMessage
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.Log.HandleOrdinaryMessage;

            /**
             * Decodes a HandleOrdinaryMessage message from the specified reader or buffer, length delimited.
             * @param reader Reader or buffer to decode from
             * @returns HandleOrdinaryMessage
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.Log.HandleOrdinaryMessage;

            /**
             * Verifies a HandleOrdinaryMessage message.
             * @param message Plain object to verify
             * @returns `null` if valid, otherwise the reason why it is not
             */
            public static verify(message: { [k: string]: any }): (string|null);

            /**
             * Creates a HandleOrdinaryMessage message from a plain object. Also converts values to their respective internal types.
             * @param object Plain object
             * @returns HandleOrdinaryMessage
             */
            public static fromObject(object: { [k: string]: any }): tracing.Log.HandleOrdinaryMessage;

            /**
             * Creates a plain object from a HandleOrdinaryMessage message. Also converts values to other types if specified.
             * @param message HandleOrdinaryMessage
             * @param [options] Conversion options
             * @returns Plain object
             */
            public static toObject(message: tracing.Log.HandleOrdinaryMessage, options?: $protobuf.IConversionOptions): { [k: string]: any };

            /**
             * Converts this HandleOrdinaryMessage to JSON.
             * @returns JSON object
             */
            public toJSON(): { [k: string]: any };
        }

        /** Properties of a SendHandshakeMessage. */
        interface ISendHandshakeMessage {

            /** SendHandshakeMessage sender */
            sender?: (string|null);

            /** SendHandshakeMessage recipient */
            recipient?: (string|null);

            /** SendHandshakeMessage record */
            record?: (tracing.Log.SendHandshakeMessage.IRecord|null);

            /** SendHandshakeMessage ping */
            ping?: (tracing.IPing|null);

            /** SendHandshakeMessage pong */
            pong?: (tracing.IPong|null);

            /** SendHandshakeMessage findNode */
            findNode?: (tracing.IFindNode|null);

            /** SendHandshakeMessage nodes */
            nodes?: (tracing.INodes|null);
        }

        /** Represents a SendHandshakeMessage. */
        class SendHandshakeMessage implements ISendHandshakeMessage {

            /**
             * Constructs a new SendHandshakeMessage.
             * @param [properties] Properties to set
             */
            constructor(properties?: tracing.Log.ISendHandshakeMessage);

            /** SendHandshakeMessage sender. */
            public sender: string;

            /** SendHandshakeMessage recipient. */
            public recipient: string;

            /** SendHandshakeMessage record. */
            public record?: (tracing.Log.SendHandshakeMessage.IRecord|null);

            /** SendHandshakeMessage ping. */
            public ping?: (tracing.IPing|null);

            /** SendHandshakeMessage pong. */
            public pong?: (tracing.IPong|null);

            /** SendHandshakeMessage findNode. */
            public findNode?: (tracing.IFindNode|null);

            /** SendHandshakeMessage nodes. */
            public nodes?: (tracing.INodes|null);

            /** SendHandshakeMessage message. */
            public message?: ("ping"|"pong"|"findNode"|"nodes");

            /**
             * Creates a new SendHandshakeMessage instance using the specified properties.
             * @param [properties] Properties to set
             * @returns SendHandshakeMessage instance
             */
            public static create(properties?: tracing.Log.ISendHandshakeMessage): tracing.Log.SendHandshakeMessage;

            /**
             * Encodes the specified SendHandshakeMessage message. Does not implicitly {@link tracing.Log.SendHandshakeMessage.verify|verify} messages.
             * @param message SendHandshakeMessage message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encode(message: tracing.Log.ISendHandshakeMessage, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Encodes the specified SendHandshakeMessage message, length delimited. Does not implicitly {@link tracing.Log.SendHandshakeMessage.verify|verify} messages.
             * @param message SendHandshakeMessage message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encodeDelimited(message: tracing.Log.ISendHandshakeMessage, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Decodes a SendHandshakeMessage message from the specified reader or buffer.
             * @param reader Reader or buffer to decode from
             * @param [length] Message length if known beforehand
             * @returns SendHandshakeMessage
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.Log.SendHandshakeMessage;

            /**
             * Decodes a SendHandshakeMessage message from the specified reader or buffer, length delimited.
             * @param reader Reader or buffer to decode from
             * @returns SendHandshakeMessage
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.Log.SendHandshakeMessage;

            /**
             * Verifies a SendHandshakeMessage message.
             * @param message Plain object to verify
             * @returns `null` if valid, otherwise the reason why it is not
             */
            public static verify(message: { [k: string]: any }): (string|null);

            /**
             * Creates a SendHandshakeMessage message from a plain object. Also converts values to their respective internal types.
             * @param object Plain object
             * @returns SendHandshakeMessage
             */
            public static fromObject(object: { [k: string]: any }): tracing.Log.SendHandshakeMessage;

            /**
             * Creates a plain object from a SendHandshakeMessage message. Also converts values to other types if specified.
             * @param message SendHandshakeMessage
             * @param [options] Conversion options
             * @returns Plain object
             */
            public static toObject(message: tracing.Log.SendHandshakeMessage, options?: $protobuf.IConversionOptions): { [k: string]: any };

            /**
             * Converts this SendHandshakeMessage to JSON.
             * @returns JSON object
             */
            public toJSON(): { [k: string]: any };
        }

        namespace SendHandshakeMessage {

            /** Properties of a Record. */
            interface IRecord {

                /** Record enrSeq */
                enrSeq?: (number|Long|null);
            }

            /** Represents a Record. */
            class Record implements IRecord {

                /**
                 * Constructs a new Record.
                 * @param [properties] Properties to set
                 */
                constructor(properties?: tracing.Log.SendHandshakeMessage.IRecord);

                /** Record enrSeq. */
                public enrSeq: (number|Long);

                /**
                 * Creates a new Record instance using the specified properties.
                 * @param [properties] Properties to set
                 * @returns Record instance
                 */
                public static create(properties?: tracing.Log.SendHandshakeMessage.IRecord): tracing.Log.SendHandshakeMessage.Record;

                /**
                 * Encodes the specified Record message. Does not implicitly {@link tracing.Log.SendHandshakeMessage.Record.verify|verify} messages.
                 * @param message Record message or plain object to encode
                 * @param [writer] Writer to encode to
                 * @returns Writer
                 */
                public static encode(message: tracing.Log.SendHandshakeMessage.IRecord, writer?: $protobuf.Writer): $protobuf.Writer;

                /**
                 * Encodes the specified Record message, length delimited. Does not implicitly {@link tracing.Log.SendHandshakeMessage.Record.verify|verify} messages.
                 * @param message Record message or plain object to encode
                 * @param [writer] Writer to encode to
                 * @returns Writer
                 */
                public static encodeDelimited(message: tracing.Log.SendHandshakeMessage.IRecord, writer?: $protobuf.Writer): $protobuf.Writer;

                /**
                 * Decodes a Record message from the specified reader or buffer.
                 * @param reader Reader or buffer to decode from
                 * @param [length] Message length if known beforehand
                 * @returns Record
                 * @throws {Error} If the payload is not a reader or valid buffer
                 * @throws {$protobuf.util.ProtocolError} If required fields are missing
                 */
                public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.Log.SendHandshakeMessage.Record;

                /**
                 * Decodes a Record message from the specified reader or buffer, length delimited.
                 * @param reader Reader or buffer to decode from
                 * @returns Record
                 * @throws {Error} If the payload is not a reader or valid buffer
                 * @throws {$protobuf.util.ProtocolError} If required fields are missing
                 */
                public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.Log.SendHandshakeMessage.Record;

                /**
                 * Verifies a Record message.
                 * @param message Plain object to verify
                 * @returns `null` if valid, otherwise the reason why it is not
                 */
                public static verify(message: { [k: string]: any }): (string|null);

                /**
                 * Creates a Record message from a plain object. Also converts values to their respective internal types.
                 * @param object Plain object
                 * @returns Record
                 */
                public static fromObject(object: { [k: string]: any }): tracing.Log.SendHandshakeMessage.Record;

                /**
                 * Creates a plain object from a Record message. Also converts values to other types if specified.
                 * @param message Record
                 * @param [options] Conversion options
                 * @returns Plain object
                 */
                public static toObject(message: tracing.Log.SendHandshakeMessage.Record, options?: $protobuf.IConversionOptions): { [k: string]: any };

                /**
                 * Converts this Record to JSON.
                 * @returns JSON object
                 */
                public toJSON(): { [k: string]: any };
            }
        }
    }

    /** Properties of a Random. */
    interface IRandom {
    }

    /** Represents a Random. */
    class Random implements IRandom {

        /**
         * Constructs a new Random.
         * @param [properties] Properties to set
         */
        constructor(properties?: tracing.IRandom);

        /**
         * Creates a new Random instance using the specified properties.
         * @param [properties] Properties to set
         * @returns Random instance
         */
        public static create(properties?: tracing.IRandom): tracing.Random;

        /**
         * Encodes the specified Random message. Does not implicitly {@link tracing.Random.verify|verify} messages.
         * @param message Random message or plain object to encode
         * @param [writer] Writer to encode to
         * @returns Writer
         */
        public static encode(message: tracing.IRandom, writer?: $protobuf.Writer): $protobuf.Writer;

        /**
         * Encodes the specified Random message, length delimited. Does not implicitly {@link tracing.Random.verify|verify} messages.
         * @param message Random message or plain object to encode
         * @param [writer] Writer to encode to
         * @returns Writer
         */
        public static encodeDelimited(message: tracing.IRandom, writer?: $protobuf.Writer): $protobuf.Writer;

        /**
         * Decodes a Random message from the specified reader or buffer.
         * @param reader Reader or buffer to decode from
         * @param [length] Message length if known beforehand
         * @returns Random
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.Random;

        /**
         * Decodes a Random message from the specified reader or buffer, length delimited.
         * @param reader Reader or buffer to decode from
         * @returns Random
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.Random;

        /**
         * Verifies a Random message.
         * @param message Plain object to verify
         * @returns `null` if valid, otherwise the reason why it is not
         */
        public static verify(message: { [k: string]: any }): (string|null);

        /**
         * Creates a Random message from a plain object. Also converts values to their respective internal types.
         * @param object Plain object
         * @returns Random
         */
        public static fromObject(object: { [k: string]: any }): tracing.Random;

        /**
         * Creates a plain object from a Random message. Also converts values to other types if specified.
         * @param message Random
         * @param [options] Conversion options
         * @returns Plain object
         */
        public static toObject(message: tracing.Random, options?: $protobuf.IConversionOptions): { [k: string]: any };

        /**
         * Converts this Random to JSON.
         * @returns JSON object
         */
        public toJSON(): { [k: string]: any };
    }

    /** Properties of a Ping. */
    interface IPing {

        /** Ping requestId */
        requestId?: (string|null);

        /** Ping enrSeq */
        enrSeq?: (number|Long|null);
    }

    /** Represents a Ping. */
    class Ping implements IPing {

        /**
         * Constructs a new Ping.
         * @param [properties] Properties to set
         */
        constructor(properties?: tracing.IPing);

        /** Ping requestId. */
        public requestId: string;

        /** Ping enrSeq. */
        public enrSeq: (number|Long);

        /**
         * Creates a new Ping instance using the specified properties.
         * @param [properties] Properties to set
         * @returns Ping instance
         */
        public static create(properties?: tracing.IPing): tracing.Ping;

        /**
         * Encodes the specified Ping message. Does not implicitly {@link tracing.Ping.verify|verify} messages.
         * @param message Ping message or plain object to encode
         * @param [writer] Writer to encode to
         * @returns Writer
         */
        public static encode(message: tracing.IPing, writer?: $protobuf.Writer): $protobuf.Writer;

        /**
         * Encodes the specified Ping message, length delimited. Does not implicitly {@link tracing.Ping.verify|verify} messages.
         * @param message Ping message or plain object to encode
         * @param [writer] Writer to encode to
         * @returns Writer
         */
        public static encodeDelimited(message: tracing.IPing, writer?: $protobuf.Writer): $protobuf.Writer;

        /**
         * Decodes a Ping message from the specified reader or buffer.
         * @param reader Reader or buffer to decode from
         * @param [length] Message length if known beforehand
         * @returns Ping
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.Ping;

        /**
         * Decodes a Ping message from the specified reader or buffer, length delimited.
         * @param reader Reader or buffer to decode from
         * @returns Ping
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.Ping;

        /**
         * Verifies a Ping message.
         * @param message Plain object to verify
         * @returns `null` if valid, otherwise the reason why it is not
         */
        public static verify(message: { [k: string]: any }): (string|null);

        /**
         * Creates a Ping message from a plain object. Also converts values to their respective internal types.
         * @param object Plain object
         * @returns Ping
         */
        public static fromObject(object: { [k: string]: any }): tracing.Ping;

        /**
         * Creates a plain object from a Ping message. Also converts values to other types if specified.
         * @param message Ping
         * @param [options] Conversion options
         * @returns Plain object
         */
        public static toObject(message: tracing.Ping, options?: $protobuf.IConversionOptions): { [k: string]: any };

        /**
         * Converts this Ping to JSON.
         * @returns JSON object
         */
        public toJSON(): { [k: string]: any };
    }

    /** Properties of a Pong. */
    interface IPong {

        /** Pong requestId */
        requestId?: (string|null);

        /** Pong enrSeq */
        enrSeq?: (number|Long|null);

        /** Pong recipientIp */
        recipientIp?: (string|null);

        /** Pong recipientPort */
        recipientPort?: (number|null);
    }

    /** Represents a Pong. */
    class Pong implements IPong {

        /**
         * Constructs a new Pong.
         * @param [properties] Properties to set
         */
        constructor(properties?: tracing.IPong);

        /** Pong requestId. */
        public requestId: string;

        /** Pong enrSeq. */
        public enrSeq: (number|Long);

        /** Pong recipientIp. */
        public recipientIp: string;

        /** Pong recipientPort. */
        public recipientPort: number;

        /**
         * Creates a new Pong instance using the specified properties.
         * @param [properties] Properties to set
         * @returns Pong instance
         */
        public static create(properties?: tracing.IPong): tracing.Pong;

        /**
         * Encodes the specified Pong message. Does not implicitly {@link tracing.Pong.verify|verify} messages.
         * @param message Pong message or plain object to encode
         * @param [writer] Writer to encode to
         * @returns Writer
         */
        public static encode(message: tracing.IPong, writer?: $protobuf.Writer): $protobuf.Writer;

        /**
         * Encodes the specified Pong message, length delimited. Does not implicitly {@link tracing.Pong.verify|verify} messages.
         * @param message Pong message or plain object to encode
         * @param [writer] Writer to encode to
         * @returns Writer
         */
        public static encodeDelimited(message: tracing.IPong, writer?: $protobuf.Writer): $protobuf.Writer;

        /**
         * Decodes a Pong message from the specified reader or buffer.
         * @param reader Reader or buffer to decode from
         * @param [length] Message length if known beforehand
         * @returns Pong
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.Pong;

        /**
         * Decodes a Pong message from the specified reader or buffer, length delimited.
         * @param reader Reader or buffer to decode from
         * @returns Pong
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.Pong;

        /**
         * Verifies a Pong message.
         * @param message Plain object to verify
         * @returns `null` if valid, otherwise the reason why it is not
         */
        public static verify(message: { [k: string]: any }): (string|null);

        /**
         * Creates a Pong message from a plain object. Also converts values to their respective internal types.
         * @param object Plain object
         * @returns Pong
         */
        public static fromObject(object: { [k: string]: any }): tracing.Pong;

        /**
         * Creates a plain object from a Pong message. Also converts values to other types if specified.
         * @param message Pong
         * @param [options] Conversion options
         * @returns Plain object
         */
        public static toObject(message: tracing.Pong, options?: $protobuf.IConversionOptions): { [k: string]: any };

        /**
         * Converts this Pong to JSON.
         * @returns JSON object
         */
        public toJSON(): { [k: string]: any };
    }

    /** Properties of a FindNode. */
    interface IFindNode {

        /** FindNode requestId */
        requestId?: (string|null);

        /** FindNode distances */
        distances?: ((number|Long)[]|null);
    }

    /** Represents a FindNode. */
    class FindNode implements IFindNode {

        /**
         * Constructs a new FindNode.
         * @param [properties] Properties to set
         */
        constructor(properties?: tracing.IFindNode);

        /** FindNode requestId. */
        public requestId: string;

        /** FindNode distances. */
        public distances: (number|Long)[];

        /**
         * Creates a new FindNode instance using the specified properties.
         * @param [properties] Properties to set
         * @returns FindNode instance
         */
        public static create(properties?: tracing.IFindNode): tracing.FindNode;

        /**
         * Encodes the specified FindNode message. Does not implicitly {@link tracing.FindNode.verify|verify} messages.
         * @param message FindNode message or plain object to encode
         * @param [writer] Writer to encode to
         * @returns Writer
         */
        public static encode(message: tracing.IFindNode, writer?: $protobuf.Writer): $protobuf.Writer;

        /**
         * Encodes the specified FindNode message, length delimited. Does not implicitly {@link tracing.FindNode.verify|verify} messages.
         * @param message FindNode message or plain object to encode
         * @param [writer] Writer to encode to
         * @returns Writer
         */
        public static encodeDelimited(message: tracing.IFindNode, writer?: $protobuf.Writer): $protobuf.Writer;

        /**
         * Decodes a FindNode message from the specified reader or buffer.
         * @param reader Reader or buffer to decode from
         * @param [length] Message length if known beforehand
         * @returns FindNode
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.FindNode;

        /**
         * Decodes a FindNode message from the specified reader or buffer, length delimited.
         * @param reader Reader or buffer to decode from
         * @returns FindNode
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.FindNode;

        /**
         * Verifies a FindNode message.
         * @param message Plain object to verify
         * @returns `null` if valid, otherwise the reason why it is not
         */
        public static verify(message: { [k: string]: any }): (string|null);

        /**
         * Creates a FindNode message from a plain object. Also converts values to their respective internal types.
         * @param object Plain object
         * @returns FindNode
         */
        public static fromObject(object: { [k: string]: any }): tracing.FindNode;

        /**
         * Creates a plain object from a FindNode message. Also converts values to other types if specified.
         * @param message FindNode
         * @param [options] Conversion options
         * @returns Plain object
         */
        public static toObject(message: tracing.FindNode, options?: $protobuf.IConversionOptions): { [k: string]: any };

        /**
         * Converts this FindNode to JSON.
         * @returns JSON object
         */
        public toJSON(): { [k: string]: any };
    }

    /** Properties of a Nodes. */
    interface INodes {

        /** Nodes requestId */
        requestId?: (string|null);

        /** Nodes total */
        total?: (number|Long|null);

        /** Nodes nodes */
        nodes?: (string[]|null);
    }

    /** Represents a Nodes. */
    class Nodes implements INodes {

        /**
         * Constructs a new Nodes.
         * @param [properties] Properties to set
         */
        constructor(properties?: tracing.INodes);

        /** Nodes requestId. */
        public requestId: string;

        /** Nodes total. */
        public total: (number|Long);

        /** Nodes nodes. */
        public nodes: string[];

        /**
         * Creates a new Nodes instance using the specified properties.
         * @param [properties] Properties to set
         * @returns Nodes instance
         */
        public static create(properties?: tracing.INodes): tracing.Nodes;

        /**
         * Encodes the specified Nodes message. Does not implicitly {@link tracing.Nodes.verify|verify} messages.
         * @param message Nodes message or plain object to encode
         * @param [writer] Writer to encode to
         * @returns Writer
         */
        public static encode(message: tracing.INodes, writer?: $protobuf.Writer): $protobuf.Writer;

        /**
         * Encodes the specified Nodes message, length delimited. Does not implicitly {@link tracing.Nodes.verify|verify} messages.
         * @param message Nodes message or plain object to encode
         * @param [writer] Writer to encode to
         * @returns Writer
         */
        public static encodeDelimited(message: tracing.INodes, writer?: $protobuf.Writer): $protobuf.Writer;

        /**
         * Decodes a Nodes message from the specified reader or buffer.
         * @param reader Reader or buffer to decode from
         * @param [length] Message length if known beforehand
         * @returns Nodes
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): tracing.Nodes;

        /**
         * Decodes a Nodes message from the specified reader or buffer, length delimited.
         * @param reader Reader or buffer to decode from
         * @returns Nodes
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): tracing.Nodes;

        /**
         * Verifies a Nodes message.
         * @param message Plain object to verify
         * @returns `null` if valid, otherwise the reason why it is not
         */
        public static verify(message: { [k: string]: any }): (string|null);

        /**
         * Creates a Nodes message from a plain object. Also converts values to their respective internal types.
         * @param object Plain object
         * @returns Nodes
         */
        public static fromObject(object: { [k: string]: any }): tracing.Nodes;

        /**
         * Creates a plain object from a Nodes message. Also converts values to other types if specified.
         * @param message Nodes
         * @param [options] Conversion options
         * @returns Plain object
         */
        public static toObject(message: tracing.Nodes, options?: $protobuf.IConversionOptions): { [k: string]: any };

        /**
         * Converts this Nodes to JSON.
         * @returns JSON object
         */
        public toJSON(): { [k: string]: any };
    }
}

/** Namespace google. */
export namespace google {

    /** Namespace protobuf. */
    namespace protobuf {

        /** Properties of a Timestamp. */
        interface ITimestamp {

            /** Timestamp seconds */
            seconds?: (number|Long|null);

            /** Timestamp nanos */
            nanos?: (number|null);
        }

        /** Represents a Timestamp. */
        class Timestamp implements ITimestamp {

            /**
             * Constructs a new Timestamp.
             * @param [properties] Properties to set
             */
            constructor(properties?: google.protobuf.ITimestamp);

            /** Timestamp seconds. */
            public seconds: (number|Long);

            /** Timestamp nanos. */
            public nanos: number;

            /**
             * Creates a new Timestamp instance using the specified properties.
             * @param [properties] Properties to set
             * @returns Timestamp instance
             */
            public static create(properties?: google.protobuf.ITimestamp): google.protobuf.Timestamp;

            /**
             * Encodes the specified Timestamp message. Does not implicitly {@link google.protobuf.Timestamp.verify|verify} messages.
             * @param message Timestamp message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encode(message: google.protobuf.ITimestamp, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Encodes the specified Timestamp message, length delimited. Does not implicitly {@link google.protobuf.Timestamp.verify|verify} messages.
             * @param message Timestamp message or plain object to encode
             * @param [writer] Writer to encode to
             * @returns Writer
             */
            public static encodeDelimited(message: google.protobuf.ITimestamp, writer?: $protobuf.Writer): $protobuf.Writer;

            /**
             * Decodes a Timestamp message from the specified reader or buffer.
             * @param reader Reader or buffer to decode from
             * @param [length] Message length if known beforehand
             * @returns Timestamp
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decode(reader: ($protobuf.Reader|Uint8Array), length?: number): google.protobuf.Timestamp;

            /**
             * Decodes a Timestamp message from the specified reader or buffer, length delimited.
             * @param reader Reader or buffer to decode from
             * @returns Timestamp
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            public static decodeDelimited(reader: ($protobuf.Reader|Uint8Array)): google.protobuf.Timestamp;

            /**
             * Verifies a Timestamp message.
             * @param message Plain object to verify
             * @returns `null` if valid, otherwise the reason why it is not
             */
            public static verify(message: { [k: string]: any }): (string|null);

            /**
             * Creates a Timestamp message from a plain object. Also converts values to their respective internal types.
             * @param object Plain object
             * @returns Timestamp
             */
            public static fromObject(object: { [k: string]: any }): google.protobuf.Timestamp;

            /**
             * Creates a plain object from a Timestamp message. Also converts values to other types if specified.
             * @param message Timestamp
             * @param [options] Conversion options
             * @returns Plain object
             */
            public static toObject(message: google.protobuf.Timestamp, options?: $protobuf.IConversionOptions): { [k: string]: any };

            /**
             * Converts this Timestamp to JSON.
             * @returns JSON object
             */
            public toJSON(): { [k: string]: any };
        }
    }
}
