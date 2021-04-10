/*eslint-disable block-scoped-var, id-length, no-control-regex, no-magic-numbers, no-prototype-builtins, no-redeclare, no-shadow, no-var, sort-vars*/
"use strict";

var $protobuf = require("protobufjs/minimal");

// Common aliases
var $Reader = $protobuf.Reader, $Writer = $protobuf.Writer, $util = $protobuf.util;

// Exported root namespace
var $root = $protobuf.roots["default"] || ($protobuf.roots["default"] = {});

$root.tracing = (function() {

    /**
     * Namespace tracing.
     * @exports tracing
     * @namespace
     */
    var tracing = {};

    tracing.Log = (function() {

        /**
         * Properties of a Log.
         * @memberof tracing
         * @interface ILog
         * @property {google.protobuf.ITimestamp|null} [timestamp] Log timestamp
         * @property {tracing.Log.IStart|null} [start] Log start
         * @property {tracing.Log.IShutdown|null} [shutdown] Log shutdown
         * @property {tracing.Log.ISendWhoAreYou|null} [sendWhoareyou] Log sendWhoareyou
         * @property {tracing.Log.ISendOrdinaryMessage|null} [sendOrdinaryMessage] Log sendOrdinaryMessage
         * @property {tracing.Log.IHandleOrdinaryMessage|null} [handleOrdinaryMessage] Log handleOrdinaryMessage
         * @property {tracing.Log.ISendHandshakeMessage|null} [sendHandshakeMessage] Log sendHandshakeMessage
         */

        /**
         * Constructs a new Log.
         * @memberof tracing
         * @classdesc Represents a Log.
         * @implements ILog
         * @constructor
         * @param {tracing.ILog=} [properties] Properties to set
         */
        function Log(properties) {
            if (properties)
                for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                    if (properties[keys[i]] != null)
                        this[keys[i]] = properties[keys[i]];
        }

        /**
         * Log timestamp.
         * @member {google.protobuf.ITimestamp|null|undefined} timestamp
         * @memberof tracing.Log
         * @instance
         */
        Log.prototype.timestamp = null;

        /**
         * Log start.
         * @member {tracing.Log.IStart|null|undefined} start
         * @memberof tracing.Log
         * @instance
         */
        Log.prototype.start = null;

        /**
         * Log shutdown.
         * @member {tracing.Log.IShutdown|null|undefined} shutdown
         * @memberof tracing.Log
         * @instance
         */
        Log.prototype.shutdown = null;

        /**
         * Log sendWhoareyou.
         * @member {tracing.Log.ISendWhoAreYou|null|undefined} sendWhoareyou
         * @memberof tracing.Log
         * @instance
         */
        Log.prototype.sendWhoareyou = null;

        /**
         * Log sendOrdinaryMessage.
         * @member {tracing.Log.ISendOrdinaryMessage|null|undefined} sendOrdinaryMessage
         * @memberof tracing.Log
         * @instance
         */
        Log.prototype.sendOrdinaryMessage = null;

        /**
         * Log handleOrdinaryMessage.
         * @member {tracing.Log.IHandleOrdinaryMessage|null|undefined} handleOrdinaryMessage
         * @memberof tracing.Log
         * @instance
         */
        Log.prototype.handleOrdinaryMessage = null;

        /**
         * Log sendHandshakeMessage.
         * @member {tracing.Log.ISendHandshakeMessage|null|undefined} sendHandshakeMessage
         * @memberof tracing.Log
         * @instance
         */
        Log.prototype.sendHandshakeMessage = null;

        // OneOf field names bound to virtual getters and setters
        var $oneOfFields;

        /**
         * Log event.
         * @member {"start"|"shutdown"|"sendWhoareyou"|"sendOrdinaryMessage"|"handleOrdinaryMessage"|"sendHandshakeMessage"|undefined} event
         * @memberof tracing.Log
         * @instance
         */
        Object.defineProperty(Log.prototype, "event", {
            get: $util.oneOfGetter($oneOfFields = ["start", "shutdown", "sendWhoareyou", "sendOrdinaryMessage", "handleOrdinaryMessage", "sendHandshakeMessage"]),
            set: $util.oneOfSetter($oneOfFields)
        });

        /**
         * Creates a new Log instance using the specified properties.
         * @function create
         * @memberof tracing.Log
         * @static
         * @param {tracing.ILog=} [properties] Properties to set
         * @returns {tracing.Log} Log instance
         */
        Log.create = function create(properties) {
            return new Log(properties);
        };

        /**
         * Encodes the specified Log message. Does not implicitly {@link tracing.Log.verify|verify} messages.
         * @function encode
         * @memberof tracing.Log
         * @static
         * @param {tracing.ILog} message Log message or plain object to encode
         * @param {$protobuf.Writer} [writer] Writer to encode to
         * @returns {$protobuf.Writer} Writer
         */
        Log.encode = function encode(message, writer) {
            if (!writer)
                writer = $Writer.create();
            if (message.timestamp != null && Object.hasOwnProperty.call(message, "timestamp"))
                $root.google.protobuf.Timestamp.encode(message.timestamp, writer.uint32(/* id 1, wireType 2 =*/10).fork()).ldelim();
            if (message.start != null && Object.hasOwnProperty.call(message, "start"))
                $root.tracing.Log.Start.encode(message.start, writer.uint32(/* id 2, wireType 2 =*/18).fork()).ldelim();
            if (message.shutdown != null && Object.hasOwnProperty.call(message, "shutdown"))
                $root.tracing.Log.Shutdown.encode(message.shutdown, writer.uint32(/* id 3, wireType 2 =*/26).fork()).ldelim();
            if (message.sendWhoareyou != null && Object.hasOwnProperty.call(message, "sendWhoareyou"))
                $root.tracing.Log.SendWhoAreYou.encode(message.sendWhoareyou, writer.uint32(/* id 4, wireType 2 =*/34).fork()).ldelim();
            if (message.sendOrdinaryMessage != null && Object.hasOwnProperty.call(message, "sendOrdinaryMessage"))
                $root.tracing.Log.SendOrdinaryMessage.encode(message.sendOrdinaryMessage, writer.uint32(/* id 5, wireType 2 =*/42).fork()).ldelim();
            if (message.handleOrdinaryMessage != null && Object.hasOwnProperty.call(message, "handleOrdinaryMessage"))
                $root.tracing.Log.HandleOrdinaryMessage.encode(message.handleOrdinaryMessage, writer.uint32(/* id 6, wireType 2 =*/50).fork()).ldelim();
            if (message.sendHandshakeMessage != null && Object.hasOwnProperty.call(message, "sendHandshakeMessage"))
                $root.tracing.Log.SendHandshakeMessage.encode(message.sendHandshakeMessage, writer.uint32(/* id 7, wireType 2 =*/58).fork()).ldelim();
            return writer;
        };

        /**
         * Encodes the specified Log message, length delimited. Does not implicitly {@link tracing.Log.verify|verify} messages.
         * @function encodeDelimited
         * @memberof tracing.Log
         * @static
         * @param {tracing.ILog} message Log message or plain object to encode
         * @param {$protobuf.Writer} [writer] Writer to encode to
         * @returns {$protobuf.Writer} Writer
         */
        Log.encodeDelimited = function encodeDelimited(message, writer) {
            return this.encode(message, writer).ldelim();
        };

        /**
         * Decodes a Log message from the specified reader or buffer.
         * @function decode
         * @memberof tracing.Log
         * @static
         * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
         * @param {number} [length] Message length if known beforehand
         * @returns {tracing.Log} Log
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        Log.decode = function decode(reader, length) {
            if (!(reader instanceof $Reader))
                reader = $Reader.create(reader);
            var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.Log();
            while (reader.pos < end) {
                var tag = reader.uint32();
                switch (tag >>> 3) {
                case 1:
                    message.timestamp = $root.google.protobuf.Timestamp.decode(reader, reader.uint32());
                    break;
                case 2:
                    message.start = $root.tracing.Log.Start.decode(reader, reader.uint32());
                    break;
                case 3:
                    message.shutdown = $root.tracing.Log.Shutdown.decode(reader, reader.uint32());
                    break;
                case 4:
                    message.sendWhoareyou = $root.tracing.Log.SendWhoAreYou.decode(reader, reader.uint32());
                    break;
                case 5:
                    message.sendOrdinaryMessage = $root.tracing.Log.SendOrdinaryMessage.decode(reader, reader.uint32());
                    break;
                case 6:
                    message.handleOrdinaryMessage = $root.tracing.Log.HandleOrdinaryMessage.decode(reader, reader.uint32());
                    break;
                case 7:
                    message.sendHandshakeMessage = $root.tracing.Log.SendHandshakeMessage.decode(reader, reader.uint32());
                    break;
                default:
                    reader.skipType(tag & 7);
                    break;
                }
            }
            return message;
        };

        /**
         * Decodes a Log message from the specified reader or buffer, length delimited.
         * @function decodeDelimited
         * @memberof tracing.Log
         * @static
         * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
         * @returns {tracing.Log} Log
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        Log.decodeDelimited = function decodeDelimited(reader) {
            if (!(reader instanceof $Reader))
                reader = new $Reader(reader);
            return this.decode(reader, reader.uint32());
        };

        /**
         * Verifies a Log message.
         * @function verify
         * @memberof tracing.Log
         * @static
         * @param {Object.<string,*>} message Plain object to verify
         * @returns {string|null} `null` if valid, otherwise the reason why it is not
         */
        Log.verify = function verify(message) {
            if (typeof message !== "object" || message === null)
                return "object expected";
            var properties = {};
            if (message.timestamp != null && message.hasOwnProperty("timestamp")) {
                var error = $root.google.protobuf.Timestamp.verify(message.timestamp);
                if (error)
                    return "timestamp." + error;
            }
            if (message.start != null && message.hasOwnProperty("start")) {
                properties.event = 1;
                {
                    var error = $root.tracing.Log.Start.verify(message.start);
                    if (error)
                        return "start." + error;
                }
            }
            if (message.shutdown != null && message.hasOwnProperty("shutdown")) {
                if (properties.event === 1)
                    return "event: multiple values";
                properties.event = 1;
                {
                    var error = $root.tracing.Log.Shutdown.verify(message.shutdown);
                    if (error)
                        return "shutdown." + error;
                }
            }
            if (message.sendWhoareyou != null && message.hasOwnProperty("sendWhoareyou")) {
                if (properties.event === 1)
                    return "event: multiple values";
                properties.event = 1;
                {
                    var error = $root.tracing.Log.SendWhoAreYou.verify(message.sendWhoareyou);
                    if (error)
                        return "sendWhoareyou." + error;
                }
            }
            if (message.sendOrdinaryMessage != null && message.hasOwnProperty("sendOrdinaryMessage")) {
                if (properties.event === 1)
                    return "event: multiple values";
                properties.event = 1;
                {
                    var error = $root.tracing.Log.SendOrdinaryMessage.verify(message.sendOrdinaryMessage);
                    if (error)
                        return "sendOrdinaryMessage." + error;
                }
            }
            if (message.handleOrdinaryMessage != null && message.hasOwnProperty("handleOrdinaryMessage")) {
                if (properties.event === 1)
                    return "event: multiple values";
                properties.event = 1;
                {
                    var error = $root.tracing.Log.HandleOrdinaryMessage.verify(message.handleOrdinaryMessage);
                    if (error)
                        return "handleOrdinaryMessage." + error;
                }
            }
            if (message.sendHandshakeMessage != null && message.hasOwnProperty("sendHandshakeMessage")) {
                if (properties.event === 1)
                    return "event: multiple values";
                properties.event = 1;
                {
                    var error = $root.tracing.Log.SendHandshakeMessage.verify(message.sendHandshakeMessage);
                    if (error)
                        return "sendHandshakeMessage." + error;
                }
            }
            return null;
        };

        /**
         * Creates a Log message from a plain object. Also converts values to their respective internal types.
         * @function fromObject
         * @memberof tracing.Log
         * @static
         * @param {Object.<string,*>} object Plain object
         * @returns {tracing.Log} Log
         */
        Log.fromObject = function fromObject(object) {
            if (object instanceof $root.tracing.Log)
                return object;
            var message = new $root.tracing.Log();
            if (object.timestamp != null) {
                if (typeof object.timestamp !== "object")
                    throw TypeError(".tracing.Log.timestamp: object expected");
                message.timestamp = $root.google.protobuf.Timestamp.fromObject(object.timestamp);
            }
            if (object.start != null) {
                if (typeof object.start !== "object")
                    throw TypeError(".tracing.Log.start: object expected");
                message.start = $root.tracing.Log.Start.fromObject(object.start);
            }
            if (object.shutdown != null) {
                if (typeof object.shutdown !== "object")
                    throw TypeError(".tracing.Log.shutdown: object expected");
                message.shutdown = $root.tracing.Log.Shutdown.fromObject(object.shutdown);
            }
            if (object.sendWhoareyou != null) {
                if (typeof object.sendWhoareyou !== "object")
                    throw TypeError(".tracing.Log.sendWhoareyou: object expected");
                message.sendWhoareyou = $root.tracing.Log.SendWhoAreYou.fromObject(object.sendWhoareyou);
            }
            if (object.sendOrdinaryMessage != null) {
                if (typeof object.sendOrdinaryMessage !== "object")
                    throw TypeError(".tracing.Log.sendOrdinaryMessage: object expected");
                message.sendOrdinaryMessage = $root.tracing.Log.SendOrdinaryMessage.fromObject(object.sendOrdinaryMessage);
            }
            if (object.handleOrdinaryMessage != null) {
                if (typeof object.handleOrdinaryMessage !== "object")
                    throw TypeError(".tracing.Log.handleOrdinaryMessage: object expected");
                message.handleOrdinaryMessage = $root.tracing.Log.HandleOrdinaryMessage.fromObject(object.handleOrdinaryMessage);
            }
            if (object.sendHandshakeMessage != null) {
                if (typeof object.sendHandshakeMessage !== "object")
                    throw TypeError(".tracing.Log.sendHandshakeMessage: object expected");
                message.sendHandshakeMessage = $root.tracing.Log.SendHandshakeMessage.fromObject(object.sendHandshakeMessage);
            }
            return message;
        };

        /**
         * Creates a plain object from a Log message. Also converts values to other types if specified.
         * @function toObject
         * @memberof tracing.Log
         * @static
         * @param {tracing.Log} message Log
         * @param {$protobuf.IConversionOptions} [options] Conversion options
         * @returns {Object.<string,*>} Plain object
         */
        Log.toObject = function toObject(message, options) {
            if (!options)
                options = {};
            var object = {};
            if (options.defaults)
                object.timestamp = null;
            if (message.timestamp != null && message.hasOwnProperty("timestamp"))
                object.timestamp = $root.google.protobuf.Timestamp.toObject(message.timestamp, options);
            if (message.start != null && message.hasOwnProperty("start")) {
                object.start = $root.tracing.Log.Start.toObject(message.start, options);
                if (options.oneofs)
                    object.event = "start";
            }
            if (message.shutdown != null && message.hasOwnProperty("shutdown")) {
                object.shutdown = $root.tracing.Log.Shutdown.toObject(message.shutdown, options);
                if (options.oneofs)
                    object.event = "shutdown";
            }
            if (message.sendWhoareyou != null && message.hasOwnProperty("sendWhoareyou")) {
                object.sendWhoareyou = $root.tracing.Log.SendWhoAreYou.toObject(message.sendWhoareyou, options);
                if (options.oneofs)
                    object.event = "sendWhoareyou";
            }
            if (message.sendOrdinaryMessage != null && message.hasOwnProperty("sendOrdinaryMessage")) {
                object.sendOrdinaryMessage = $root.tracing.Log.SendOrdinaryMessage.toObject(message.sendOrdinaryMessage, options);
                if (options.oneofs)
                    object.event = "sendOrdinaryMessage";
            }
            if (message.handleOrdinaryMessage != null && message.hasOwnProperty("handleOrdinaryMessage")) {
                object.handleOrdinaryMessage = $root.tracing.Log.HandleOrdinaryMessage.toObject(message.handleOrdinaryMessage, options);
                if (options.oneofs)
                    object.event = "handleOrdinaryMessage";
            }
            if (message.sendHandshakeMessage != null && message.hasOwnProperty("sendHandshakeMessage")) {
                object.sendHandshakeMessage = $root.tracing.Log.SendHandshakeMessage.toObject(message.sendHandshakeMessage, options);
                if (options.oneofs)
                    object.event = "sendHandshakeMessage";
            }
            return object;
        };

        /**
         * Converts this Log to JSON.
         * @function toJSON
         * @memberof tracing.Log
         * @instance
         * @returns {Object.<string,*>} JSON object
         */
        Log.prototype.toJSON = function toJSON() {
            return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
        };

        Log.Start = (function() {

            /**
             * Properties of a Start.
             * @memberof tracing.Log
             * @interface IStart
             * @property {string|null} [nodeId] Start nodeId
             */

            /**
             * Constructs a new Start.
             * @memberof tracing.Log
             * @classdesc Represents a Start.
             * @implements IStart
             * @constructor
             * @param {tracing.Log.IStart=} [properties] Properties to set
             */
            function Start(properties) {
                if (properties)
                    for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                        if (properties[keys[i]] != null)
                            this[keys[i]] = properties[keys[i]];
            }

            /**
             * Start nodeId.
             * @member {string} nodeId
             * @memberof tracing.Log.Start
             * @instance
             */
            Start.prototype.nodeId = "";

            /**
             * Creates a new Start instance using the specified properties.
             * @function create
             * @memberof tracing.Log.Start
             * @static
             * @param {tracing.Log.IStart=} [properties] Properties to set
             * @returns {tracing.Log.Start} Start instance
             */
            Start.create = function create(properties) {
                return new Start(properties);
            };

            /**
             * Encodes the specified Start message. Does not implicitly {@link tracing.Log.Start.verify|verify} messages.
             * @function encode
             * @memberof tracing.Log.Start
             * @static
             * @param {tracing.Log.IStart} message Start message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            Start.encode = function encode(message, writer) {
                if (!writer)
                    writer = $Writer.create();
                if (message.nodeId != null && Object.hasOwnProperty.call(message, "nodeId"))
                    writer.uint32(/* id 1, wireType 2 =*/10).string(message.nodeId);
                return writer;
            };

            /**
             * Encodes the specified Start message, length delimited. Does not implicitly {@link tracing.Log.Start.verify|verify} messages.
             * @function encodeDelimited
             * @memberof tracing.Log.Start
             * @static
             * @param {tracing.Log.IStart} message Start message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            Start.encodeDelimited = function encodeDelimited(message, writer) {
                return this.encode(message, writer).ldelim();
            };

            /**
             * Decodes a Start message from the specified reader or buffer.
             * @function decode
             * @memberof tracing.Log.Start
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @param {number} [length] Message length if known beforehand
             * @returns {tracing.Log.Start} Start
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            Start.decode = function decode(reader, length) {
                if (!(reader instanceof $Reader))
                    reader = $Reader.create(reader);
                var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.Log.Start();
                while (reader.pos < end) {
                    var tag = reader.uint32();
                    switch (tag >>> 3) {
                    case 1:
                        message.nodeId = reader.string();
                        break;
                    default:
                        reader.skipType(tag & 7);
                        break;
                    }
                }
                return message;
            };

            /**
             * Decodes a Start message from the specified reader or buffer, length delimited.
             * @function decodeDelimited
             * @memberof tracing.Log.Start
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @returns {tracing.Log.Start} Start
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            Start.decodeDelimited = function decodeDelimited(reader) {
                if (!(reader instanceof $Reader))
                    reader = new $Reader(reader);
                return this.decode(reader, reader.uint32());
            };

            /**
             * Verifies a Start message.
             * @function verify
             * @memberof tracing.Log.Start
             * @static
             * @param {Object.<string,*>} message Plain object to verify
             * @returns {string|null} `null` if valid, otherwise the reason why it is not
             */
            Start.verify = function verify(message) {
                if (typeof message !== "object" || message === null)
                    return "object expected";
                if (message.nodeId != null && message.hasOwnProperty("nodeId"))
                    if (!$util.isString(message.nodeId))
                        return "nodeId: string expected";
                return null;
            };

            /**
             * Creates a Start message from a plain object. Also converts values to their respective internal types.
             * @function fromObject
             * @memberof tracing.Log.Start
             * @static
             * @param {Object.<string,*>} object Plain object
             * @returns {tracing.Log.Start} Start
             */
            Start.fromObject = function fromObject(object) {
                if (object instanceof $root.tracing.Log.Start)
                    return object;
                var message = new $root.tracing.Log.Start();
                if (object.nodeId != null)
                    message.nodeId = String(object.nodeId);
                return message;
            };

            /**
             * Creates a plain object from a Start message. Also converts values to other types if specified.
             * @function toObject
             * @memberof tracing.Log.Start
             * @static
             * @param {tracing.Log.Start} message Start
             * @param {$protobuf.IConversionOptions} [options] Conversion options
             * @returns {Object.<string,*>} Plain object
             */
            Start.toObject = function toObject(message, options) {
                if (!options)
                    options = {};
                var object = {};
                if (options.defaults)
                    object.nodeId = "";
                if (message.nodeId != null && message.hasOwnProperty("nodeId"))
                    object.nodeId = message.nodeId;
                return object;
            };

            /**
             * Converts this Start to JSON.
             * @function toJSON
             * @memberof tracing.Log.Start
             * @instance
             * @returns {Object.<string,*>} JSON object
             */
            Start.prototype.toJSON = function toJSON() {
                return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
            };

            return Start;
        })();

        Log.Shutdown = (function() {

            /**
             * Properties of a Shutdown.
             * @memberof tracing.Log
             * @interface IShutdown
             * @property {string|null} [nodeId] Shutdown nodeId
             */

            /**
             * Constructs a new Shutdown.
             * @memberof tracing.Log
             * @classdesc Represents a Shutdown.
             * @implements IShutdown
             * @constructor
             * @param {tracing.Log.IShutdown=} [properties] Properties to set
             */
            function Shutdown(properties) {
                if (properties)
                    for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                        if (properties[keys[i]] != null)
                            this[keys[i]] = properties[keys[i]];
            }

            /**
             * Shutdown nodeId.
             * @member {string} nodeId
             * @memberof tracing.Log.Shutdown
             * @instance
             */
            Shutdown.prototype.nodeId = "";

            /**
             * Creates a new Shutdown instance using the specified properties.
             * @function create
             * @memberof tracing.Log.Shutdown
             * @static
             * @param {tracing.Log.IShutdown=} [properties] Properties to set
             * @returns {tracing.Log.Shutdown} Shutdown instance
             */
            Shutdown.create = function create(properties) {
                return new Shutdown(properties);
            };

            /**
             * Encodes the specified Shutdown message. Does not implicitly {@link tracing.Log.Shutdown.verify|verify} messages.
             * @function encode
             * @memberof tracing.Log.Shutdown
             * @static
             * @param {tracing.Log.IShutdown} message Shutdown message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            Shutdown.encode = function encode(message, writer) {
                if (!writer)
                    writer = $Writer.create();
                if (message.nodeId != null && Object.hasOwnProperty.call(message, "nodeId"))
                    writer.uint32(/* id 1, wireType 2 =*/10).string(message.nodeId);
                return writer;
            };

            /**
             * Encodes the specified Shutdown message, length delimited. Does not implicitly {@link tracing.Log.Shutdown.verify|verify} messages.
             * @function encodeDelimited
             * @memberof tracing.Log.Shutdown
             * @static
             * @param {tracing.Log.IShutdown} message Shutdown message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            Shutdown.encodeDelimited = function encodeDelimited(message, writer) {
                return this.encode(message, writer).ldelim();
            };

            /**
             * Decodes a Shutdown message from the specified reader or buffer.
             * @function decode
             * @memberof tracing.Log.Shutdown
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @param {number} [length] Message length if known beforehand
             * @returns {tracing.Log.Shutdown} Shutdown
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            Shutdown.decode = function decode(reader, length) {
                if (!(reader instanceof $Reader))
                    reader = $Reader.create(reader);
                var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.Log.Shutdown();
                while (reader.pos < end) {
                    var tag = reader.uint32();
                    switch (tag >>> 3) {
                    case 1:
                        message.nodeId = reader.string();
                        break;
                    default:
                        reader.skipType(tag & 7);
                        break;
                    }
                }
                return message;
            };

            /**
             * Decodes a Shutdown message from the specified reader or buffer, length delimited.
             * @function decodeDelimited
             * @memberof tracing.Log.Shutdown
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @returns {tracing.Log.Shutdown} Shutdown
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            Shutdown.decodeDelimited = function decodeDelimited(reader) {
                if (!(reader instanceof $Reader))
                    reader = new $Reader(reader);
                return this.decode(reader, reader.uint32());
            };

            /**
             * Verifies a Shutdown message.
             * @function verify
             * @memberof tracing.Log.Shutdown
             * @static
             * @param {Object.<string,*>} message Plain object to verify
             * @returns {string|null} `null` if valid, otherwise the reason why it is not
             */
            Shutdown.verify = function verify(message) {
                if (typeof message !== "object" || message === null)
                    return "object expected";
                if (message.nodeId != null && message.hasOwnProperty("nodeId"))
                    if (!$util.isString(message.nodeId))
                        return "nodeId: string expected";
                return null;
            };

            /**
             * Creates a Shutdown message from a plain object. Also converts values to their respective internal types.
             * @function fromObject
             * @memberof tracing.Log.Shutdown
             * @static
             * @param {Object.<string,*>} object Plain object
             * @returns {tracing.Log.Shutdown} Shutdown
             */
            Shutdown.fromObject = function fromObject(object) {
                if (object instanceof $root.tracing.Log.Shutdown)
                    return object;
                var message = new $root.tracing.Log.Shutdown();
                if (object.nodeId != null)
                    message.nodeId = String(object.nodeId);
                return message;
            };

            /**
             * Creates a plain object from a Shutdown message. Also converts values to other types if specified.
             * @function toObject
             * @memberof tracing.Log.Shutdown
             * @static
             * @param {tracing.Log.Shutdown} message Shutdown
             * @param {$protobuf.IConversionOptions} [options] Conversion options
             * @returns {Object.<string,*>} Plain object
             */
            Shutdown.toObject = function toObject(message, options) {
                if (!options)
                    options = {};
                var object = {};
                if (options.defaults)
                    object.nodeId = "";
                if (message.nodeId != null && message.hasOwnProperty("nodeId"))
                    object.nodeId = message.nodeId;
                return object;
            };

            /**
             * Converts this Shutdown to JSON.
             * @function toJSON
             * @memberof tracing.Log.Shutdown
             * @instance
             * @returns {Object.<string,*>} JSON object
             */
            Shutdown.prototype.toJSON = function toJSON() {
                return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
            };

            return Shutdown;
        })();

        Log.SendWhoAreYou = (function() {

            /**
             * Properties of a SendWhoAreYou.
             * @memberof tracing.Log
             * @interface ISendWhoAreYou
             * @property {string|null} [sender] SendWhoAreYou sender
             * @property {string|null} [recipient] SendWhoAreYou recipient
             * @property {Array.<number>|null} [idNonce] SendWhoAreYou idNonce
             * @property {number|Long|null} [enrSeq] SendWhoAreYou enrSeq
             */

            /**
             * Constructs a new SendWhoAreYou.
             * @memberof tracing.Log
             * @classdesc Represents a SendWhoAreYou.
             * @implements ISendWhoAreYou
             * @constructor
             * @param {tracing.Log.ISendWhoAreYou=} [properties] Properties to set
             */
            function SendWhoAreYou(properties) {
                this.idNonce = [];
                if (properties)
                    for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                        if (properties[keys[i]] != null)
                            this[keys[i]] = properties[keys[i]];
            }

            /**
             * SendWhoAreYou sender.
             * @member {string} sender
             * @memberof tracing.Log.SendWhoAreYou
             * @instance
             */
            SendWhoAreYou.prototype.sender = "";

            /**
             * SendWhoAreYou recipient.
             * @member {string} recipient
             * @memberof tracing.Log.SendWhoAreYou
             * @instance
             */
            SendWhoAreYou.prototype.recipient = "";

            /**
             * SendWhoAreYou idNonce.
             * @member {Array.<number>} idNonce
             * @memberof tracing.Log.SendWhoAreYou
             * @instance
             */
            SendWhoAreYou.prototype.idNonce = $util.emptyArray;

            /**
             * SendWhoAreYou enrSeq.
             * @member {number|Long} enrSeq
             * @memberof tracing.Log.SendWhoAreYou
             * @instance
             */
            SendWhoAreYou.prototype.enrSeq = $util.Long ? $util.Long.fromBits(0,0,true) : 0;

            /**
             * Creates a new SendWhoAreYou instance using the specified properties.
             * @function create
             * @memberof tracing.Log.SendWhoAreYou
             * @static
             * @param {tracing.Log.ISendWhoAreYou=} [properties] Properties to set
             * @returns {tracing.Log.SendWhoAreYou} SendWhoAreYou instance
             */
            SendWhoAreYou.create = function create(properties) {
                return new SendWhoAreYou(properties);
            };

            /**
             * Encodes the specified SendWhoAreYou message. Does not implicitly {@link tracing.Log.SendWhoAreYou.verify|verify} messages.
             * @function encode
             * @memberof tracing.Log.SendWhoAreYou
             * @static
             * @param {tracing.Log.ISendWhoAreYou} message SendWhoAreYou message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            SendWhoAreYou.encode = function encode(message, writer) {
                if (!writer)
                    writer = $Writer.create();
                if (message.sender != null && Object.hasOwnProperty.call(message, "sender"))
                    writer.uint32(/* id 1, wireType 2 =*/10).string(message.sender);
                if (message.recipient != null && Object.hasOwnProperty.call(message, "recipient"))
                    writer.uint32(/* id 2, wireType 2 =*/18).string(message.recipient);
                if (message.idNonce != null && message.idNonce.length) {
                    writer.uint32(/* id 3, wireType 2 =*/26).fork();
                    for (var i = 0; i < message.idNonce.length; ++i)
                        writer.uint32(message.idNonce[i]);
                    writer.ldelim();
                }
                if (message.enrSeq != null && Object.hasOwnProperty.call(message, "enrSeq"))
                    writer.uint32(/* id 4, wireType 0 =*/32).uint64(message.enrSeq);
                return writer;
            };

            /**
             * Encodes the specified SendWhoAreYou message, length delimited. Does not implicitly {@link tracing.Log.SendWhoAreYou.verify|verify} messages.
             * @function encodeDelimited
             * @memberof tracing.Log.SendWhoAreYou
             * @static
             * @param {tracing.Log.ISendWhoAreYou} message SendWhoAreYou message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            SendWhoAreYou.encodeDelimited = function encodeDelimited(message, writer) {
                return this.encode(message, writer).ldelim();
            };

            /**
             * Decodes a SendWhoAreYou message from the specified reader or buffer.
             * @function decode
             * @memberof tracing.Log.SendWhoAreYou
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @param {number} [length] Message length if known beforehand
             * @returns {tracing.Log.SendWhoAreYou} SendWhoAreYou
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            SendWhoAreYou.decode = function decode(reader, length) {
                if (!(reader instanceof $Reader))
                    reader = $Reader.create(reader);
                var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.Log.SendWhoAreYou();
                while (reader.pos < end) {
                    var tag = reader.uint32();
                    switch (tag >>> 3) {
                    case 1:
                        message.sender = reader.string();
                        break;
                    case 2:
                        message.recipient = reader.string();
                        break;
                    case 3:
                        if (!(message.idNonce && message.idNonce.length))
                            message.idNonce = [];
                        if ((tag & 7) === 2) {
                            var end2 = reader.uint32() + reader.pos;
                            while (reader.pos < end2)
                                message.idNonce.push(reader.uint32());
                        } else
                            message.idNonce.push(reader.uint32());
                        break;
                    case 4:
                        message.enrSeq = reader.uint64();
                        break;
                    default:
                        reader.skipType(tag & 7);
                        break;
                    }
                }
                return message;
            };

            /**
             * Decodes a SendWhoAreYou message from the specified reader or buffer, length delimited.
             * @function decodeDelimited
             * @memberof tracing.Log.SendWhoAreYou
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @returns {tracing.Log.SendWhoAreYou} SendWhoAreYou
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            SendWhoAreYou.decodeDelimited = function decodeDelimited(reader) {
                if (!(reader instanceof $Reader))
                    reader = new $Reader(reader);
                return this.decode(reader, reader.uint32());
            };

            /**
             * Verifies a SendWhoAreYou message.
             * @function verify
             * @memberof tracing.Log.SendWhoAreYou
             * @static
             * @param {Object.<string,*>} message Plain object to verify
             * @returns {string|null} `null` if valid, otherwise the reason why it is not
             */
            SendWhoAreYou.verify = function verify(message) {
                if (typeof message !== "object" || message === null)
                    return "object expected";
                if (message.sender != null && message.hasOwnProperty("sender"))
                    if (!$util.isString(message.sender))
                        return "sender: string expected";
                if (message.recipient != null && message.hasOwnProperty("recipient"))
                    if (!$util.isString(message.recipient))
                        return "recipient: string expected";
                if (message.idNonce != null && message.hasOwnProperty("idNonce")) {
                    if (!Array.isArray(message.idNonce))
                        return "idNonce: array expected";
                    for (var i = 0; i < message.idNonce.length; ++i)
                        if (!$util.isInteger(message.idNonce[i]))
                            return "idNonce: integer[] expected";
                }
                if (message.enrSeq != null && message.hasOwnProperty("enrSeq"))
                    if (!$util.isInteger(message.enrSeq) && !(message.enrSeq && $util.isInteger(message.enrSeq.low) && $util.isInteger(message.enrSeq.high)))
                        return "enrSeq: integer|Long expected";
                return null;
            };

            /**
             * Creates a SendWhoAreYou message from a plain object. Also converts values to their respective internal types.
             * @function fromObject
             * @memberof tracing.Log.SendWhoAreYou
             * @static
             * @param {Object.<string,*>} object Plain object
             * @returns {tracing.Log.SendWhoAreYou} SendWhoAreYou
             */
            SendWhoAreYou.fromObject = function fromObject(object) {
                if (object instanceof $root.tracing.Log.SendWhoAreYou)
                    return object;
                var message = new $root.tracing.Log.SendWhoAreYou();
                if (object.sender != null)
                    message.sender = String(object.sender);
                if (object.recipient != null)
                    message.recipient = String(object.recipient);
                if (object.idNonce) {
                    if (!Array.isArray(object.idNonce))
                        throw TypeError(".tracing.Log.SendWhoAreYou.idNonce: array expected");
                    message.idNonce = [];
                    for (var i = 0; i < object.idNonce.length; ++i)
                        message.idNonce[i] = object.idNonce[i] >>> 0;
                }
                if (object.enrSeq != null)
                    if ($util.Long)
                        (message.enrSeq = $util.Long.fromValue(object.enrSeq)).unsigned = true;
                    else if (typeof object.enrSeq === "string")
                        message.enrSeq = parseInt(object.enrSeq, 10);
                    else if (typeof object.enrSeq === "number")
                        message.enrSeq = object.enrSeq;
                    else if (typeof object.enrSeq === "object")
                        message.enrSeq = new $util.LongBits(object.enrSeq.low >>> 0, object.enrSeq.high >>> 0).toNumber(true);
                return message;
            };

            /**
             * Creates a plain object from a SendWhoAreYou message. Also converts values to other types if specified.
             * @function toObject
             * @memberof tracing.Log.SendWhoAreYou
             * @static
             * @param {tracing.Log.SendWhoAreYou} message SendWhoAreYou
             * @param {$protobuf.IConversionOptions} [options] Conversion options
             * @returns {Object.<string,*>} Plain object
             */
            SendWhoAreYou.toObject = function toObject(message, options) {
                if (!options)
                    options = {};
                var object = {};
                if (options.arrays || options.defaults)
                    object.idNonce = [];
                if (options.defaults) {
                    object.sender = "";
                    object.recipient = "";
                    if ($util.Long) {
                        var long = new $util.Long(0, 0, true);
                        object.enrSeq = options.longs === String ? long.toString() : options.longs === Number ? long.toNumber() : long;
                    } else
                        object.enrSeq = options.longs === String ? "0" : 0;
                }
                if (message.sender != null && message.hasOwnProperty("sender"))
                    object.sender = message.sender;
                if (message.recipient != null && message.hasOwnProperty("recipient"))
                    object.recipient = message.recipient;
                if (message.idNonce && message.idNonce.length) {
                    object.idNonce = [];
                    for (var j = 0; j < message.idNonce.length; ++j)
                        object.idNonce[j] = message.idNonce[j];
                }
                if (message.enrSeq != null && message.hasOwnProperty("enrSeq"))
                    if (typeof message.enrSeq === "number")
                        object.enrSeq = options.longs === String ? String(message.enrSeq) : message.enrSeq;
                    else
                        object.enrSeq = options.longs === String ? $util.Long.prototype.toString.call(message.enrSeq) : options.longs === Number ? new $util.LongBits(message.enrSeq.low >>> 0, message.enrSeq.high >>> 0).toNumber(true) : message.enrSeq;
                return object;
            };

            /**
             * Converts this SendWhoAreYou to JSON.
             * @function toJSON
             * @memberof tracing.Log.SendWhoAreYou
             * @instance
             * @returns {Object.<string,*>} JSON object
             */
            SendWhoAreYou.prototype.toJSON = function toJSON() {
                return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
            };

            return SendWhoAreYou;
        })();

        Log.SendOrdinaryMessage = (function() {

            /**
             * Properties of a SendOrdinaryMessage.
             * @memberof tracing.Log
             * @interface ISendOrdinaryMessage
             * @property {string|null} [sender] SendOrdinaryMessage sender
             * @property {string|null} [recipient] SendOrdinaryMessage recipient
             * @property {tracing.IRandom|null} [random] SendOrdinaryMessage random
             * @property {tracing.IPing|null} [ping] SendOrdinaryMessage ping
             * @property {tracing.IPong|null} [pong] SendOrdinaryMessage pong
             * @property {tracing.IFindNode|null} [findNode] SendOrdinaryMessage findNode
             * @property {tracing.INodes|null} [nodes] SendOrdinaryMessage nodes
             */

            /**
             * Constructs a new SendOrdinaryMessage.
             * @memberof tracing.Log
             * @classdesc Represents a SendOrdinaryMessage.
             * @implements ISendOrdinaryMessage
             * @constructor
             * @param {tracing.Log.ISendOrdinaryMessage=} [properties] Properties to set
             */
            function SendOrdinaryMessage(properties) {
                if (properties)
                    for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                        if (properties[keys[i]] != null)
                            this[keys[i]] = properties[keys[i]];
            }

            /**
             * SendOrdinaryMessage sender.
             * @member {string} sender
             * @memberof tracing.Log.SendOrdinaryMessage
             * @instance
             */
            SendOrdinaryMessage.prototype.sender = "";

            /**
             * SendOrdinaryMessage recipient.
             * @member {string} recipient
             * @memberof tracing.Log.SendOrdinaryMessage
             * @instance
             */
            SendOrdinaryMessage.prototype.recipient = "";

            /**
             * SendOrdinaryMessage random.
             * @member {tracing.IRandom|null|undefined} random
             * @memberof tracing.Log.SendOrdinaryMessage
             * @instance
             */
            SendOrdinaryMessage.prototype.random = null;

            /**
             * SendOrdinaryMessage ping.
             * @member {tracing.IPing|null|undefined} ping
             * @memberof tracing.Log.SendOrdinaryMessage
             * @instance
             */
            SendOrdinaryMessage.prototype.ping = null;

            /**
             * SendOrdinaryMessage pong.
             * @member {tracing.IPong|null|undefined} pong
             * @memberof tracing.Log.SendOrdinaryMessage
             * @instance
             */
            SendOrdinaryMessage.prototype.pong = null;

            /**
             * SendOrdinaryMessage findNode.
             * @member {tracing.IFindNode|null|undefined} findNode
             * @memberof tracing.Log.SendOrdinaryMessage
             * @instance
             */
            SendOrdinaryMessage.prototype.findNode = null;

            /**
             * SendOrdinaryMessage nodes.
             * @member {tracing.INodes|null|undefined} nodes
             * @memberof tracing.Log.SendOrdinaryMessage
             * @instance
             */
            SendOrdinaryMessage.prototype.nodes = null;

            // OneOf field names bound to virtual getters and setters
            var $oneOfFields;

            /**
             * SendOrdinaryMessage message.
             * @member {"random"|"ping"|"pong"|"findNode"|"nodes"|undefined} message
             * @memberof tracing.Log.SendOrdinaryMessage
             * @instance
             */
            Object.defineProperty(SendOrdinaryMessage.prototype, "message", {
                get: $util.oneOfGetter($oneOfFields = ["random", "ping", "pong", "findNode", "nodes"]),
                set: $util.oneOfSetter($oneOfFields)
            });

            /**
             * Creates a new SendOrdinaryMessage instance using the specified properties.
             * @function create
             * @memberof tracing.Log.SendOrdinaryMessage
             * @static
             * @param {tracing.Log.ISendOrdinaryMessage=} [properties] Properties to set
             * @returns {tracing.Log.SendOrdinaryMessage} SendOrdinaryMessage instance
             */
            SendOrdinaryMessage.create = function create(properties) {
                return new SendOrdinaryMessage(properties);
            };

            /**
             * Encodes the specified SendOrdinaryMessage message. Does not implicitly {@link tracing.Log.SendOrdinaryMessage.verify|verify} messages.
             * @function encode
             * @memberof tracing.Log.SendOrdinaryMessage
             * @static
             * @param {tracing.Log.ISendOrdinaryMessage} message SendOrdinaryMessage message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            SendOrdinaryMessage.encode = function encode(message, writer) {
                if (!writer)
                    writer = $Writer.create();
                if (message.sender != null && Object.hasOwnProperty.call(message, "sender"))
                    writer.uint32(/* id 1, wireType 2 =*/10).string(message.sender);
                if (message.recipient != null && Object.hasOwnProperty.call(message, "recipient"))
                    writer.uint32(/* id 2, wireType 2 =*/18).string(message.recipient);
                if (message.random != null && Object.hasOwnProperty.call(message, "random"))
                    $root.tracing.Random.encode(message.random, writer.uint32(/* id 3, wireType 2 =*/26).fork()).ldelim();
                if (message.ping != null && Object.hasOwnProperty.call(message, "ping"))
                    $root.tracing.Ping.encode(message.ping, writer.uint32(/* id 4, wireType 2 =*/34).fork()).ldelim();
                if (message.pong != null && Object.hasOwnProperty.call(message, "pong"))
                    $root.tracing.Pong.encode(message.pong, writer.uint32(/* id 5, wireType 2 =*/42).fork()).ldelim();
                if (message.findNode != null && Object.hasOwnProperty.call(message, "findNode"))
                    $root.tracing.FindNode.encode(message.findNode, writer.uint32(/* id 6, wireType 2 =*/50).fork()).ldelim();
                if (message.nodes != null && Object.hasOwnProperty.call(message, "nodes"))
                    $root.tracing.Nodes.encode(message.nodes, writer.uint32(/* id 7, wireType 2 =*/58).fork()).ldelim();
                return writer;
            };

            /**
             * Encodes the specified SendOrdinaryMessage message, length delimited. Does not implicitly {@link tracing.Log.SendOrdinaryMessage.verify|verify} messages.
             * @function encodeDelimited
             * @memberof tracing.Log.SendOrdinaryMessage
             * @static
             * @param {tracing.Log.ISendOrdinaryMessage} message SendOrdinaryMessage message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            SendOrdinaryMessage.encodeDelimited = function encodeDelimited(message, writer) {
                return this.encode(message, writer).ldelim();
            };

            /**
             * Decodes a SendOrdinaryMessage message from the specified reader or buffer.
             * @function decode
             * @memberof tracing.Log.SendOrdinaryMessage
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @param {number} [length] Message length if known beforehand
             * @returns {tracing.Log.SendOrdinaryMessage} SendOrdinaryMessage
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            SendOrdinaryMessage.decode = function decode(reader, length) {
                if (!(reader instanceof $Reader))
                    reader = $Reader.create(reader);
                var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.Log.SendOrdinaryMessage();
                while (reader.pos < end) {
                    var tag = reader.uint32();
                    switch (tag >>> 3) {
                    case 1:
                        message.sender = reader.string();
                        break;
                    case 2:
                        message.recipient = reader.string();
                        break;
                    case 3:
                        message.random = $root.tracing.Random.decode(reader, reader.uint32());
                        break;
                    case 4:
                        message.ping = $root.tracing.Ping.decode(reader, reader.uint32());
                        break;
                    case 5:
                        message.pong = $root.tracing.Pong.decode(reader, reader.uint32());
                        break;
                    case 6:
                        message.findNode = $root.tracing.FindNode.decode(reader, reader.uint32());
                        break;
                    case 7:
                        message.nodes = $root.tracing.Nodes.decode(reader, reader.uint32());
                        break;
                    default:
                        reader.skipType(tag & 7);
                        break;
                    }
                }
                return message;
            };

            /**
             * Decodes a SendOrdinaryMessage message from the specified reader or buffer, length delimited.
             * @function decodeDelimited
             * @memberof tracing.Log.SendOrdinaryMessage
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @returns {tracing.Log.SendOrdinaryMessage} SendOrdinaryMessage
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            SendOrdinaryMessage.decodeDelimited = function decodeDelimited(reader) {
                if (!(reader instanceof $Reader))
                    reader = new $Reader(reader);
                return this.decode(reader, reader.uint32());
            };

            /**
             * Verifies a SendOrdinaryMessage message.
             * @function verify
             * @memberof tracing.Log.SendOrdinaryMessage
             * @static
             * @param {Object.<string,*>} message Plain object to verify
             * @returns {string|null} `null` if valid, otherwise the reason why it is not
             */
            SendOrdinaryMessage.verify = function verify(message) {
                if (typeof message !== "object" || message === null)
                    return "object expected";
                var properties = {};
                if (message.sender != null && message.hasOwnProperty("sender"))
                    if (!$util.isString(message.sender))
                        return "sender: string expected";
                if (message.recipient != null && message.hasOwnProperty("recipient"))
                    if (!$util.isString(message.recipient))
                        return "recipient: string expected";
                if (message.random != null && message.hasOwnProperty("random")) {
                    properties.message = 1;
                    {
                        var error = $root.tracing.Random.verify(message.random);
                        if (error)
                            return "random." + error;
                    }
                }
                if (message.ping != null && message.hasOwnProperty("ping")) {
                    if (properties.message === 1)
                        return "message: multiple values";
                    properties.message = 1;
                    {
                        var error = $root.tracing.Ping.verify(message.ping);
                        if (error)
                            return "ping." + error;
                    }
                }
                if (message.pong != null && message.hasOwnProperty("pong")) {
                    if (properties.message === 1)
                        return "message: multiple values";
                    properties.message = 1;
                    {
                        var error = $root.tracing.Pong.verify(message.pong);
                        if (error)
                            return "pong." + error;
                    }
                }
                if (message.findNode != null && message.hasOwnProperty("findNode")) {
                    if (properties.message === 1)
                        return "message: multiple values";
                    properties.message = 1;
                    {
                        var error = $root.tracing.FindNode.verify(message.findNode);
                        if (error)
                            return "findNode." + error;
                    }
                }
                if (message.nodes != null && message.hasOwnProperty("nodes")) {
                    if (properties.message === 1)
                        return "message: multiple values";
                    properties.message = 1;
                    {
                        var error = $root.tracing.Nodes.verify(message.nodes);
                        if (error)
                            return "nodes." + error;
                    }
                }
                return null;
            };

            /**
             * Creates a SendOrdinaryMessage message from a plain object. Also converts values to their respective internal types.
             * @function fromObject
             * @memberof tracing.Log.SendOrdinaryMessage
             * @static
             * @param {Object.<string,*>} object Plain object
             * @returns {tracing.Log.SendOrdinaryMessage} SendOrdinaryMessage
             */
            SendOrdinaryMessage.fromObject = function fromObject(object) {
                if (object instanceof $root.tracing.Log.SendOrdinaryMessage)
                    return object;
                var message = new $root.tracing.Log.SendOrdinaryMessage();
                if (object.sender != null)
                    message.sender = String(object.sender);
                if (object.recipient != null)
                    message.recipient = String(object.recipient);
                if (object.random != null) {
                    if (typeof object.random !== "object")
                        throw TypeError(".tracing.Log.SendOrdinaryMessage.random: object expected");
                    message.random = $root.tracing.Random.fromObject(object.random);
                }
                if (object.ping != null) {
                    if (typeof object.ping !== "object")
                        throw TypeError(".tracing.Log.SendOrdinaryMessage.ping: object expected");
                    message.ping = $root.tracing.Ping.fromObject(object.ping);
                }
                if (object.pong != null) {
                    if (typeof object.pong !== "object")
                        throw TypeError(".tracing.Log.SendOrdinaryMessage.pong: object expected");
                    message.pong = $root.tracing.Pong.fromObject(object.pong);
                }
                if (object.findNode != null) {
                    if (typeof object.findNode !== "object")
                        throw TypeError(".tracing.Log.SendOrdinaryMessage.findNode: object expected");
                    message.findNode = $root.tracing.FindNode.fromObject(object.findNode);
                }
                if (object.nodes != null) {
                    if (typeof object.nodes !== "object")
                        throw TypeError(".tracing.Log.SendOrdinaryMessage.nodes: object expected");
                    message.nodes = $root.tracing.Nodes.fromObject(object.nodes);
                }
                return message;
            };

            /**
             * Creates a plain object from a SendOrdinaryMessage message. Also converts values to other types if specified.
             * @function toObject
             * @memberof tracing.Log.SendOrdinaryMessage
             * @static
             * @param {tracing.Log.SendOrdinaryMessage} message SendOrdinaryMessage
             * @param {$protobuf.IConversionOptions} [options] Conversion options
             * @returns {Object.<string,*>} Plain object
             */
            SendOrdinaryMessage.toObject = function toObject(message, options) {
                if (!options)
                    options = {};
                var object = {};
                if (options.defaults) {
                    object.sender = "";
                    object.recipient = "";
                }
                if (message.sender != null && message.hasOwnProperty("sender"))
                    object.sender = message.sender;
                if (message.recipient != null && message.hasOwnProperty("recipient"))
                    object.recipient = message.recipient;
                if (message.random != null && message.hasOwnProperty("random")) {
                    object.random = $root.tracing.Random.toObject(message.random, options);
                    if (options.oneofs)
                        object.message = "random";
                }
                if (message.ping != null && message.hasOwnProperty("ping")) {
                    object.ping = $root.tracing.Ping.toObject(message.ping, options);
                    if (options.oneofs)
                        object.message = "ping";
                }
                if (message.pong != null && message.hasOwnProperty("pong")) {
                    object.pong = $root.tracing.Pong.toObject(message.pong, options);
                    if (options.oneofs)
                        object.message = "pong";
                }
                if (message.findNode != null && message.hasOwnProperty("findNode")) {
                    object.findNode = $root.tracing.FindNode.toObject(message.findNode, options);
                    if (options.oneofs)
                        object.message = "findNode";
                }
                if (message.nodes != null && message.hasOwnProperty("nodes")) {
                    object.nodes = $root.tracing.Nodes.toObject(message.nodes, options);
                    if (options.oneofs)
                        object.message = "nodes";
                }
                return object;
            };

            /**
             * Converts this SendOrdinaryMessage to JSON.
             * @function toJSON
             * @memberof tracing.Log.SendOrdinaryMessage
             * @instance
             * @returns {Object.<string,*>} JSON object
             */
            SendOrdinaryMessage.prototype.toJSON = function toJSON() {
                return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
            };

            return SendOrdinaryMessage;
        })();

        Log.HandleOrdinaryMessage = (function() {

            /**
             * Properties of a HandleOrdinaryMessage.
             * @memberof tracing.Log
             * @interface IHandleOrdinaryMessage
             * @property {string|null} [sender] HandleOrdinaryMessage sender
             * @property {string|null} [recipient] HandleOrdinaryMessage recipient
             * @property {tracing.IRandom|null} [random] HandleOrdinaryMessage random
             * @property {tracing.IPing|null} [ping] HandleOrdinaryMessage ping
             * @property {tracing.IPong|null} [pong] HandleOrdinaryMessage pong
             * @property {tracing.IFindNode|null} [findNode] HandleOrdinaryMessage findNode
             * @property {tracing.INodes|null} [nodes] HandleOrdinaryMessage nodes
             */

            /**
             * Constructs a new HandleOrdinaryMessage.
             * @memberof tracing.Log
             * @classdesc Represents a HandleOrdinaryMessage.
             * @implements IHandleOrdinaryMessage
             * @constructor
             * @param {tracing.Log.IHandleOrdinaryMessage=} [properties] Properties to set
             */
            function HandleOrdinaryMessage(properties) {
                if (properties)
                    for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                        if (properties[keys[i]] != null)
                            this[keys[i]] = properties[keys[i]];
            }

            /**
             * HandleOrdinaryMessage sender.
             * @member {string} sender
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @instance
             */
            HandleOrdinaryMessage.prototype.sender = "";

            /**
             * HandleOrdinaryMessage recipient.
             * @member {string} recipient
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @instance
             */
            HandleOrdinaryMessage.prototype.recipient = "";

            /**
             * HandleOrdinaryMessage random.
             * @member {tracing.IRandom|null|undefined} random
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @instance
             */
            HandleOrdinaryMessage.prototype.random = null;

            /**
             * HandleOrdinaryMessage ping.
             * @member {tracing.IPing|null|undefined} ping
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @instance
             */
            HandleOrdinaryMessage.prototype.ping = null;

            /**
             * HandleOrdinaryMessage pong.
             * @member {tracing.IPong|null|undefined} pong
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @instance
             */
            HandleOrdinaryMessage.prototype.pong = null;

            /**
             * HandleOrdinaryMessage findNode.
             * @member {tracing.IFindNode|null|undefined} findNode
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @instance
             */
            HandleOrdinaryMessage.prototype.findNode = null;

            /**
             * HandleOrdinaryMessage nodes.
             * @member {tracing.INodes|null|undefined} nodes
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @instance
             */
            HandleOrdinaryMessage.prototype.nodes = null;

            // OneOf field names bound to virtual getters and setters
            var $oneOfFields;

            /**
             * HandleOrdinaryMessage message.
             * @member {"random"|"ping"|"pong"|"findNode"|"nodes"|undefined} message
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @instance
             */
            Object.defineProperty(HandleOrdinaryMessage.prototype, "message", {
                get: $util.oneOfGetter($oneOfFields = ["random", "ping", "pong", "findNode", "nodes"]),
                set: $util.oneOfSetter($oneOfFields)
            });

            /**
             * Creates a new HandleOrdinaryMessage instance using the specified properties.
             * @function create
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @static
             * @param {tracing.Log.IHandleOrdinaryMessage=} [properties] Properties to set
             * @returns {tracing.Log.HandleOrdinaryMessage} HandleOrdinaryMessage instance
             */
            HandleOrdinaryMessage.create = function create(properties) {
                return new HandleOrdinaryMessage(properties);
            };

            /**
             * Encodes the specified HandleOrdinaryMessage message. Does not implicitly {@link tracing.Log.HandleOrdinaryMessage.verify|verify} messages.
             * @function encode
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @static
             * @param {tracing.Log.IHandleOrdinaryMessage} message HandleOrdinaryMessage message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            HandleOrdinaryMessage.encode = function encode(message, writer) {
                if (!writer)
                    writer = $Writer.create();
                if (message.sender != null && Object.hasOwnProperty.call(message, "sender"))
                    writer.uint32(/* id 1, wireType 2 =*/10).string(message.sender);
                if (message.recipient != null && Object.hasOwnProperty.call(message, "recipient"))
                    writer.uint32(/* id 2, wireType 2 =*/18).string(message.recipient);
                if (message.random != null && Object.hasOwnProperty.call(message, "random"))
                    $root.tracing.Random.encode(message.random, writer.uint32(/* id 3, wireType 2 =*/26).fork()).ldelim();
                if (message.ping != null && Object.hasOwnProperty.call(message, "ping"))
                    $root.tracing.Ping.encode(message.ping, writer.uint32(/* id 4, wireType 2 =*/34).fork()).ldelim();
                if (message.pong != null && Object.hasOwnProperty.call(message, "pong"))
                    $root.tracing.Pong.encode(message.pong, writer.uint32(/* id 5, wireType 2 =*/42).fork()).ldelim();
                if (message.findNode != null && Object.hasOwnProperty.call(message, "findNode"))
                    $root.tracing.FindNode.encode(message.findNode, writer.uint32(/* id 6, wireType 2 =*/50).fork()).ldelim();
                if (message.nodes != null && Object.hasOwnProperty.call(message, "nodes"))
                    $root.tracing.Nodes.encode(message.nodes, writer.uint32(/* id 7, wireType 2 =*/58).fork()).ldelim();
                return writer;
            };

            /**
             * Encodes the specified HandleOrdinaryMessage message, length delimited. Does not implicitly {@link tracing.Log.HandleOrdinaryMessage.verify|verify} messages.
             * @function encodeDelimited
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @static
             * @param {tracing.Log.IHandleOrdinaryMessage} message HandleOrdinaryMessage message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            HandleOrdinaryMessage.encodeDelimited = function encodeDelimited(message, writer) {
                return this.encode(message, writer).ldelim();
            };

            /**
             * Decodes a HandleOrdinaryMessage message from the specified reader or buffer.
             * @function decode
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @param {number} [length] Message length if known beforehand
             * @returns {tracing.Log.HandleOrdinaryMessage} HandleOrdinaryMessage
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            HandleOrdinaryMessage.decode = function decode(reader, length) {
                if (!(reader instanceof $Reader))
                    reader = $Reader.create(reader);
                var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.Log.HandleOrdinaryMessage();
                while (reader.pos < end) {
                    var tag = reader.uint32();
                    switch (tag >>> 3) {
                    case 1:
                        message.sender = reader.string();
                        break;
                    case 2:
                        message.recipient = reader.string();
                        break;
                    case 3:
                        message.random = $root.tracing.Random.decode(reader, reader.uint32());
                        break;
                    case 4:
                        message.ping = $root.tracing.Ping.decode(reader, reader.uint32());
                        break;
                    case 5:
                        message.pong = $root.tracing.Pong.decode(reader, reader.uint32());
                        break;
                    case 6:
                        message.findNode = $root.tracing.FindNode.decode(reader, reader.uint32());
                        break;
                    case 7:
                        message.nodes = $root.tracing.Nodes.decode(reader, reader.uint32());
                        break;
                    default:
                        reader.skipType(tag & 7);
                        break;
                    }
                }
                return message;
            };

            /**
             * Decodes a HandleOrdinaryMessage message from the specified reader or buffer, length delimited.
             * @function decodeDelimited
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @returns {tracing.Log.HandleOrdinaryMessage} HandleOrdinaryMessage
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            HandleOrdinaryMessage.decodeDelimited = function decodeDelimited(reader) {
                if (!(reader instanceof $Reader))
                    reader = new $Reader(reader);
                return this.decode(reader, reader.uint32());
            };

            /**
             * Verifies a HandleOrdinaryMessage message.
             * @function verify
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @static
             * @param {Object.<string,*>} message Plain object to verify
             * @returns {string|null} `null` if valid, otherwise the reason why it is not
             */
            HandleOrdinaryMessage.verify = function verify(message) {
                if (typeof message !== "object" || message === null)
                    return "object expected";
                var properties = {};
                if (message.sender != null && message.hasOwnProperty("sender"))
                    if (!$util.isString(message.sender))
                        return "sender: string expected";
                if (message.recipient != null && message.hasOwnProperty("recipient"))
                    if (!$util.isString(message.recipient))
                        return "recipient: string expected";
                if (message.random != null && message.hasOwnProperty("random")) {
                    properties.message = 1;
                    {
                        var error = $root.tracing.Random.verify(message.random);
                        if (error)
                            return "random." + error;
                    }
                }
                if (message.ping != null && message.hasOwnProperty("ping")) {
                    if (properties.message === 1)
                        return "message: multiple values";
                    properties.message = 1;
                    {
                        var error = $root.tracing.Ping.verify(message.ping);
                        if (error)
                            return "ping." + error;
                    }
                }
                if (message.pong != null && message.hasOwnProperty("pong")) {
                    if (properties.message === 1)
                        return "message: multiple values";
                    properties.message = 1;
                    {
                        var error = $root.tracing.Pong.verify(message.pong);
                        if (error)
                            return "pong." + error;
                    }
                }
                if (message.findNode != null && message.hasOwnProperty("findNode")) {
                    if (properties.message === 1)
                        return "message: multiple values";
                    properties.message = 1;
                    {
                        var error = $root.tracing.FindNode.verify(message.findNode);
                        if (error)
                            return "findNode." + error;
                    }
                }
                if (message.nodes != null && message.hasOwnProperty("nodes")) {
                    if (properties.message === 1)
                        return "message: multiple values";
                    properties.message = 1;
                    {
                        var error = $root.tracing.Nodes.verify(message.nodes);
                        if (error)
                            return "nodes." + error;
                    }
                }
                return null;
            };

            /**
             * Creates a HandleOrdinaryMessage message from a plain object. Also converts values to their respective internal types.
             * @function fromObject
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @static
             * @param {Object.<string,*>} object Plain object
             * @returns {tracing.Log.HandleOrdinaryMessage} HandleOrdinaryMessage
             */
            HandleOrdinaryMessage.fromObject = function fromObject(object) {
                if (object instanceof $root.tracing.Log.HandleOrdinaryMessage)
                    return object;
                var message = new $root.tracing.Log.HandleOrdinaryMessage();
                if (object.sender != null)
                    message.sender = String(object.sender);
                if (object.recipient != null)
                    message.recipient = String(object.recipient);
                if (object.random != null) {
                    if (typeof object.random !== "object")
                        throw TypeError(".tracing.Log.HandleOrdinaryMessage.random: object expected");
                    message.random = $root.tracing.Random.fromObject(object.random);
                }
                if (object.ping != null) {
                    if (typeof object.ping !== "object")
                        throw TypeError(".tracing.Log.HandleOrdinaryMessage.ping: object expected");
                    message.ping = $root.tracing.Ping.fromObject(object.ping);
                }
                if (object.pong != null) {
                    if (typeof object.pong !== "object")
                        throw TypeError(".tracing.Log.HandleOrdinaryMessage.pong: object expected");
                    message.pong = $root.tracing.Pong.fromObject(object.pong);
                }
                if (object.findNode != null) {
                    if (typeof object.findNode !== "object")
                        throw TypeError(".tracing.Log.HandleOrdinaryMessage.findNode: object expected");
                    message.findNode = $root.tracing.FindNode.fromObject(object.findNode);
                }
                if (object.nodes != null) {
                    if (typeof object.nodes !== "object")
                        throw TypeError(".tracing.Log.HandleOrdinaryMessage.nodes: object expected");
                    message.nodes = $root.tracing.Nodes.fromObject(object.nodes);
                }
                return message;
            };

            /**
             * Creates a plain object from a HandleOrdinaryMessage message. Also converts values to other types if specified.
             * @function toObject
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @static
             * @param {tracing.Log.HandleOrdinaryMessage} message HandleOrdinaryMessage
             * @param {$protobuf.IConversionOptions} [options] Conversion options
             * @returns {Object.<string,*>} Plain object
             */
            HandleOrdinaryMessage.toObject = function toObject(message, options) {
                if (!options)
                    options = {};
                var object = {};
                if (options.defaults) {
                    object.sender = "";
                    object.recipient = "";
                }
                if (message.sender != null && message.hasOwnProperty("sender"))
                    object.sender = message.sender;
                if (message.recipient != null && message.hasOwnProperty("recipient"))
                    object.recipient = message.recipient;
                if (message.random != null && message.hasOwnProperty("random")) {
                    object.random = $root.tracing.Random.toObject(message.random, options);
                    if (options.oneofs)
                        object.message = "random";
                }
                if (message.ping != null && message.hasOwnProperty("ping")) {
                    object.ping = $root.tracing.Ping.toObject(message.ping, options);
                    if (options.oneofs)
                        object.message = "ping";
                }
                if (message.pong != null && message.hasOwnProperty("pong")) {
                    object.pong = $root.tracing.Pong.toObject(message.pong, options);
                    if (options.oneofs)
                        object.message = "pong";
                }
                if (message.findNode != null && message.hasOwnProperty("findNode")) {
                    object.findNode = $root.tracing.FindNode.toObject(message.findNode, options);
                    if (options.oneofs)
                        object.message = "findNode";
                }
                if (message.nodes != null && message.hasOwnProperty("nodes")) {
                    object.nodes = $root.tracing.Nodes.toObject(message.nodes, options);
                    if (options.oneofs)
                        object.message = "nodes";
                }
                return object;
            };

            /**
             * Converts this HandleOrdinaryMessage to JSON.
             * @function toJSON
             * @memberof tracing.Log.HandleOrdinaryMessage
             * @instance
             * @returns {Object.<string,*>} JSON object
             */
            HandleOrdinaryMessage.prototype.toJSON = function toJSON() {
                return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
            };

            return HandleOrdinaryMessage;
        })();

        Log.SendHandshakeMessage = (function() {

            /**
             * Properties of a SendHandshakeMessage.
             * @memberof tracing.Log
             * @interface ISendHandshakeMessage
             * @property {string|null} [sender] SendHandshakeMessage sender
             * @property {string|null} [recipient] SendHandshakeMessage recipient
             * @property {tracing.Log.SendHandshakeMessage.IRecord|null} [record] SendHandshakeMessage record
             * @property {tracing.IPing|null} [ping] SendHandshakeMessage ping
             * @property {tracing.IPong|null} [pong] SendHandshakeMessage pong
             * @property {tracing.IFindNode|null} [findNode] SendHandshakeMessage findNode
             * @property {tracing.INodes|null} [nodes] SendHandshakeMessage nodes
             */

            /**
             * Constructs a new SendHandshakeMessage.
             * @memberof tracing.Log
             * @classdesc Represents a SendHandshakeMessage.
             * @implements ISendHandshakeMessage
             * @constructor
             * @param {tracing.Log.ISendHandshakeMessage=} [properties] Properties to set
             */
            function SendHandshakeMessage(properties) {
                if (properties)
                    for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                        if (properties[keys[i]] != null)
                            this[keys[i]] = properties[keys[i]];
            }

            /**
             * SendHandshakeMessage sender.
             * @member {string} sender
             * @memberof tracing.Log.SendHandshakeMessage
             * @instance
             */
            SendHandshakeMessage.prototype.sender = "";

            /**
             * SendHandshakeMessage recipient.
             * @member {string} recipient
             * @memberof tracing.Log.SendHandshakeMessage
             * @instance
             */
            SendHandshakeMessage.prototype.recipient = "";

            /**
             * SendHandshakeMessage record.
             * @member {tracing.Log.SendHandshakeMessage.IRecord|null|undefined} record
             * @memberof tracing.Log.SendHandshakeMessage
             * @instance
             */
            SendHandshakeMessage.prototype.record = null;

            /**
             * SendHandshakeMessage ping.
             * @member {tracing.IPing|null|undefined} ping
             * @memberof tracing.Log.SendHandshakeMessage
             * @instance
             */
            SendHandshakeMessage.prototype.ping = null;

            /**
             * SendHandshakeMessage pong.
             * @member {tracing.IPong|null|undefined} pong
             * @memberof tracing.Log.SendHandshakeMessage
             * @instance
             */
            SendHandshakeMessage.prototype.pong = null;

            /**
             * SendHandshakeMessage findNode.
             * @member {tracing.IFindNode|null|undefined} findNode
             * @memberof tracing.Log.SendHandshakeMessage
             * @instance
             */
            SendHandshakeMessage.prototype.findNode = null;

            /**
             * SendHandshakeMessage nodes.
             * @member {tracing.INodes|null|undefined} nodes
             * @memberof tracing.Log.SendHandshakeMessage
             * @instance
             */
            SendHandshakeMessage.prototype.nodes = null;

            // OneOf field names bound to virtual getters and setters
            var $oneOfFields;

            /**
             * SendHandshakeMessage message.
             * @member {"ping"|"pong"|"findNode"|"nodes"|undefined} message
             * @memberof tracing.Log.SendHandshakeMessage
             * @instance
             */
            Object.defineProperty(SendHandshakeMessage.prototype, "message", {
                get: $util.oneOfGetter($oneOfFields = ["ping", "pong", "findNode", "nodes"]),
                set: $util.oneOfSetter($oneOfFields)
            });

            /**
             * Creates a new SendHandshakeMessage instance using the specified properties.
             * @function create
             * @memberof tracing.Log.SendHandshakeMessage
             * @static
             * @param {tracing.Log.ISendHandshakeMessage=} [properties] Properties to set
             * @returns {tracing.Log.SendHandshakeMessage} SendHandshakeMessage instance
             */
            SendHandshakeMessage.create = function create(properties) {
                return new SendHandshakeMessage(properties);
            };

            /**
             * Encodes the specified SendHandshakeMessage message. Does not implicitly {@link tracing.Log.SendHandshakeMessage.verify|verify} messages.
             * @function encode
             * @memberof tracing.Log.SendHandshakeMessage
             * @static
             * @param {tracing.Log.ISendHandshakeMessage} message SendHandshakeMessage message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            SendHandshakeMessage.encode = function encode(message, writer) {
                if (!writer)
                    writer = $Writer.create();
                if (message.sender != null && Object.hasOwnProperty.call(message, "sender"))
                    writer.uint32(/* id 1, wireType 2 =*/10).string(message.sender);
                if (message.recipient != null && Object.hasOwnProperty.call(message, "recipient"))
                    writer.uint32(/* id 2, wireType 2 =*/18).string(message.recipient);
                if (message.record != null && Object.hasOwnProperty.call(message, "record"))
                    $root.tracing.Log.SendHandshakeMessage.Record.encode(message.record, writer.uint32(/* id 3, wireType 2 =*/26).fork()).ldelim();
                if (message.ping != null && Object.hasOwnProperty.call(message, "ping"))
                    $root.tracing.Ping.encode(message.ping, writer.uint32(/* id 4, wireType 2 =*/34).fork()).ldelim();
                if (message.pong != null && Object.hasOwnProperty.call(message, "pong"))
                    $root.tracing.Pong.encode(message.pong, writer.uint32(/* id 5, wireType 2 =*/42).fork()).ldelim();
                if (message.findNode != null && Object.hasOwnProperty.call(message, "findNode"))
                    $root.tracing.FindNode.encode(message.findNode, writer.uint32(/* id 6, wireType 2 =*/50).fork()).ldelim();
                if (message.nodes != null && Object.hasOwnProperty.call(message, "nodes"))
                    $root.tracing.Nodes.encode(message.nodes, writer.uint32(/* id 7, wireType 2 =*/58).fork()).ldelim();
                return writer;
            };

            /**
             * Encodes the specified SendHandshakeMessage message, length delimited. Does not implicitly {@link tracing.Log.SendHandshakeMessage.verify|verify} messages.
             * @function encodeDelimited
             * @memberof tracing.Log.SendHandshakeMessage
             * @static
             * @param {tracing.Log.ISendHandshakeMessage} message SendHandshakeMessage message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            SendHandshakeMessage.encodeDelimited = function encodeDelimited(message, writer) {
                return this.encode(message, writer).ldelim();
            };

            /**
             * Decodes a SendHandshakeMessage message from the specified reader or buffer.
             * @function decode
             * @memberof tracing.Log.SendHandshakeMessage
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @param {number} [length] Message length if known beforehand
             * @returns {tracing.Log.SendHandshakeMessage} SendHandshakeMessage
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            SendHandshakeMessage.decode = function decode(reader, length) {
                if (!(reader instanceof $Reader))
                    reader = $Reader.create(reader);
                var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.Log.SendHandshakeMessage();
                while (reader.pos < end) {
                    var tag = reader.uint32();
                    switch (tag >>> 3) {
                    case 1:
                        message.sender = reader.string();
                        break;
                    case 2:
                        message.recipient = reader.string();
                        break;
                    case 3:
                        message.record = $root.tracing.Log.SendHandshakeMessage.Record.decode(reader, reader.uint32());
                        break;
                    case 4:
                        message.ping = $root.tracing.Ping.decode(reader, reader.uint32());
                        break;
                    case 5:
                        message.pong = $root.tracing.Pong.decode(reader, reader.uint32());
                        break;
                    case 6:
                        message.findNode = $root.tracing.FindNode.decode(reader, reader.uint32());
                        break;
                    case 7:
                        message.nodes = $root.tracing.Nodes.decode(reader, reader.uint32());
                        break;
                    default:
                        reader.skipType(tag & 7);
                        break;
                    }
                }
                return message;
            };

            /**
             * Decodes a SendHandshakeMessage message from the specified reader or buffer, length delimited.
             * @function decodeDelimited
             * @memberof tracing.Log.SendHandshakeMessage
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @returns {tracing.Log.SendHandshakeMessage} SendHandshakeMessage
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            SendHandshakeMessage.decodeDelimited = function decodeDelimited(reader) {
                if (!(reader instanceof $Reader))
                    reader = new $Reader(reader);
                return this.decode(reader, reader.uint32());
            };

            /**
             * Verifies a SendHandshakeMessage message.
             * @function verify
             * @memberof tracing.Log.SendHandshakeMessage
             * @static
             * @param {Object.<string,*>} message Plain object to verify
             * @returns {string|null} `null` if valid, otherwise the reason why it is not
             */
            SendHandshakeMessage.verify = function verify(message) {
                if (typeof message !== "object" || message === null)
                    return "object expected";
                var properties = {};
                if (message.sender != null && message.hasOwnProperty("sender"))
                    if (!$util.isString(message.sender))
                        return "sender: string expected";
                if (message.recipient != null && message.hasOwnProperty("recipient"))
                    if (!$util.isString(message.recipient))
                        return "recipient: string expected";
                if (message.record != null && message.hasOwnProperty("record")) {
                    var error = $root.tracing.Log.SendHandshakeMessage.Record.verify(message.record);
                    if (error)
                        return "record." + error;
                }
                if (message.ping != null && message.hasOwnProperty("ping")) {
                    properties.message = 1;
                    {
                        var error = $root.tracing.Ping.verify(message.ping);
                        if (error)
                            return "ping." + error;
                    }
                }
                if (message.pong != null && message.hasOwnProperty("pong")) {
                    if (properties.message === 1)
                        return "message: multiple values";
                    properties.message = 1;
                    {
                        var error = $root.tracing.Pong.verify(message.pong);
                        if (error)
                            return "pong." + error;
                    }
                }
                if (message.findNode != null && message.hasOwnProperty("findNode")) {
                    if (properties.message === 1)
                        return "message: multiple values";
                    properties.message = 1;
                    {
                        var error = $root.tracing.FindNode.verify(message.findNode);
                        if (error)
                            return "findNode." + error;
                    }
                }
                if (message.nodes != null && message.hasOwnProperty("nodes")) {
                    if (properties.message === 1)
                        return "message: multiple values";
                    properties.message = 1;
                    {
                        var error = $root.tracing.Nodes.verify(message.nodes);
                        if (error)
                            return "nodes." + error;
                    }
                }
                return null;
            };

            /**
             * Creates a SendHandshakeMessage message from a plain object. Also converts values to their respective internal types.
             * @function fromObject
             * @memberof tracing.Log.SendHandshakeMessage
             * @static
             * @param {Object.<string,*>} object Plain object
             * @returns {tracing.Log.SendHandshakeMessage} SendHandshakeMessage
             */
            SendHandshakeMessage.fromObject = function fromObject(object) {
                if (object instanceof $root.tracing.Log.SendHandshakeMessage)
                    return object;
                var message = new $root.tracing.Log.SendHandshakeMessage();
                if (object.sender != null)
                    message.sender = String(object.sender);
                if (object.recipient != null)
                    message.recipient = String(object.recipient);
                if (object.record != null) {
                    if (typeof object.record !== "object")
                        throw TypeError(".tracing.Log.SendHandshakeMessage.record: object expected");
                    message.record = $root.tracing.Log.SendHandshakeMessage.Record.fromObject(object.record);
                }
                if (object.ping != null) {
                    if (typeof object.ping !== "object")
                        throw TypeError(".tracing.Log.SendHandshakeMessage.ping: object expected");
                    message.ping = $root.tracing.Ping.fromObject(object.ping);
                }
                if (object.pong != null) {
                    if (typeof object.pong !== "object")
                        throw TypeError(".tracing.Log.SendHandshakeMessage.pong: object expected");
                    message.pong = $root.tracing.Pong.fromObject(object.pong);
                }
                if (object.findNode != null) {
                    if (typeof object.findNode !== "object")
                        throw TypeError(".tracing.Log.SendHandshakeMessage.findNode: object expected");
                    message.findNode = $root.tracing.FindNode.fromObject(object.findNode);
                }
                if (object.nodes != null) {
                    if (typeof object.nodes !== "object")
                        throw TypeError(".tracing.Log.SendHandshakeMessage.nodes: object expected");
                    message.nodes = $root.tracing.Nodes.fromObject(object.nodes);
                }
                return message;
            };

            /**
             * Creates a plain object from a SendHandshakeMessage message. Also converts values to other types if specified.
             * @function toObject
             * @memberof tracing.Log.SendHandshakeMessage
             * @static
             * @param {tracing.Log.SendHandshakeMessage} message SendHandshakeMessage
             * @param {$protobuf.IConversionOptions} [options] Conversion options
             * @returns {Object.<string,*>} Plain object
             */
            SendHandshakeMessage.toObject = function toObject(message, options) {
                if (!options)
                    options = {};
                var object = {};
                if (options.defaults) {
                    object.sender = "";
                    object.recipient = "";
                    object.record = null;
                }
                if (message.sender != null && message.hasOwnProperty("sender"))
                    object.sender = message.sender;
                if (message.recipient != null && message.hasOwnProperty("recipient"))
                    object.recipient = message.recipient;
                if (message.record != null && message.hasOwnProperty("record"))
                    object.record = $root.tracing.Log.SendHandshakeMessage.Record.toObject(message.record, options);
                if (message.ping != null && message.hasOwnProperty("ping")) {
                    object.ping = $root.tracing.Ping.toObject(message.ping, options);
                    if (options.oneofs)
                        object.message = "ping";
                }
                if (message.pong != null && message.hasOwnProperty("pong")) {
                    object.pong = $root.tracing.Pong.toObject(message.pong, options);
                    if (options.oneofs)
                        object.message = "pong";
                }
                if (message.findNode != null && message.hasOwnProperty("findNode")) {
                    object.findNode = $root.tracing.FindNode.toObject(message.findNode, options);
                    if (options.oneofs)
                        object.message = "findNode";
                }
                if (message.nodes != null && message.hasOwnProperty("nodes")) {
                    object.nodes = $root.tracing.Nodes.toObject(message.nodes, options);
                    if (options.oneofs)
                        object.message = "nodes";
                }
                return object;
            };

            /**
             * Converts this SendHandshakeMessage to JSON.
             * @function toJSON
             * @memberof tracing.Log.SendHandshakeMessage
             * @instance
             * @returns {Object.<string,*>} JSON object
             */
            SendHandshakeMessage.prototype.toJSON = function toJSON() {
                return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
            };

            SendHandshakeMessage.Record = (function() {

                /**
                 * Properties of a Record.
                 * @memberof tracing.Log.SendHandshakeMessage
                 * @interface IRecord
                 * @property {number|Long|null} [enrSeq] Record enrSeq
                 */

                /**
                 * Constructs a new Record.
                 * @memberof tracing.Log.SendHandshakeMessage
                 * @classdesc Represents a Record.
                 * @implements IRecord
                 * @constructor
                 * @param {tracing.Log.SendHandshakeMessage.IRecord=} [properties] Properties to set
                 */
                function Record(properties) {
                    if (properties)
                        for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                            if (properties[keys[i]] != null)
                                this[keys[i]] = properties[keys[i]];
                }

                /**
                 * Record enrSeq.
                 * @member {number|Long} enrSeq
                 * @memberof tracing.Log.SendHandshakeMessage.Record
                 * @instance
                 */
                Record.prototype.enrSeq = $util.Long ? $util.Long.fromBits(0,0,true) : 0;

                /**
                 * Creates a new Record instance using the specified properties.
                 * @function create
                 * @memberof tracing.Log.SendHandshakeMessage.Record
                 * @static
                 * @param {tracing.Log.SendHandshakeMessage.IRecord=} [properties] Properties to set
                 * @returns {tracing.Log.SendHandshakeMessage.Record} Record instance
                 */
                Record.create = function create(properties) {
                    return new Record(properties);
                };

                /**
                 * Encodes the specified Record message. Does not implicitly {@link tracing.Log.SendHandshakeMessage.Record.verify|verify} messages.
                 * @function encode
                 * @memberof tracing.Log.SendHandshakeMessage.Record
                 * @static
                 * @param {tracing.Log.SendHandshakeMessage.IRecord} message Record message or plain object to encode
                 * @param {$protobuf.Writer} [writer] Writer to encode to
                 * @returns {$protobuf.Writer} Writer
                 */
                Record.encode = function encode(message, writer) {
                    if (!writer)
                        writer = $Writer.create();
                    if (message.enrSeq != null && Object.hasOwnProperty.call(message, "enrSeq"))
                        writer.uint32(/* id 1, wireType 0 =*/8).uint64(message.enrSeq);
                    return writer;
                };

                /**
                 * Encodes the specified Record message, length delimited. Does not implicitly {@link tracing.Log.SendHandshakeMessage.Record.verify|verify} messages.
                 * @function encodeDelimited
                 * @memberof tracing.Log.SendHandshakeMessage.Record
                 * @static
                 * @param {tracing.Log.SendHandshakeMessage.IRecord} message Record message or plain object to encode
                 * @param {$protobuf.Writer} [writer] Writer to encode to
                 * @returns {$protobuf.Writer} Writer
                 */
                Record.encodeDelimited = function encodeDelimited(message, writer) {
                    return this.encode(message, writer).ldelim();
                };

                /**
                 * Decodes a Record message from the specified reader or buffer.
                 * @function decode
                 * @memberof tracing.Log.SendHandshakeMessage.Record
                 * @static
                 * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
                 * @param {number} [length] Message length if known beforehand
                 * @returns {tracing.Log.SendHandshakeMessage.Record} Record
                 * @throws {Error} If the payload is not a reader or valid buffer
                 * @throws {$protobuf.util.ProtocolError} If required fields are missing
                 */
                Record.decode = function decode(reader, length) {
                    if (!(reader instanceof $Reader))
                        reader = $Reader.create(reader);
                    var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.Log.SendHandshakeMessage.Record();
                    while (reader.pos < end) {
                        var tag = reader.uint32();
                        switch (tag >>> 3) {
                        case 1:
                            message.enrSeq = reader.uint64();
                            break;
                        default:
                            reader.skipType(tag & 7);
                            break;
                        }
                    }
                    return message;
                };

                /**
                 * Decodes a Record message from the specified reader or buffer, length delimited.
                 * @function decodeDelimited
                 * @memberof tracing.Log.SendHandshakeMessage.Record
                 * @static
                 * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
                 * @returns {tracing.Log.SendHandshakeMessage.Record} Record
                 * @throws {Error} If the payload is not a reader or valid buffer
                 * @throws {$protobuf.util.ProtocolError} If required fields are missing
                 */
                Record.decodeDelimited = function decodeDelimited(reader) {
                    if (!(reader instanceof $Reader))
                        reader = new $Reader(reader);
                    return this.decode(reader, reader.uint32());
                };

                /**
                 * Verifies a Record message.
                 * @function verify
                 * @memberof tracing.Log.SendHandshakeMessage.Record
                 * @static
                 * @param {Object.<string,*>} message Plain object to verify
                 * @returns {string|null} `null` if valid, otherwise the reason why it is not
                 */
                Record.verify = function verify(message) {
                    if (typeof message !== "object" || message === null)
                        return "object expected";
                    if (message.enrSeq != null && message.hasOwnProperty("enrSeq"))
                        if (!$util.isInteger(message.enrSeq) && !(message.enrSeq && $util.isInteger(message.enrSeq.low) && $util.isInteger(message.enrSeq.high)))
                            return "enrSeq: integer|Long expected";
                    return null;
                };

                /**
                 * Creates a Record message from a plain object. Also converts values to their respective internal types.
                 * @function fromObject
                 * @memberof tracing.Log.SendHandshakeMessage.Record
                 * @static
                 * @param {Object.<string,*>} object Plain object
                 * @returns {tracing.Log.SendHandshakeMessage.Record} Record
                 */
                Record.fromObject = function fromObject(object) {
                    if (object instanceof $root.tracing.Log.SendHandshakeMessage.Record)
                        return object;
                    var message = new $root.tracing.Log.SendHandshakeMessage.Record();
                    if (object.enrSeq != null)
                        if ($util.Long)
                            (message.enrSeq = $util.Long.fromValue(object.enrSeq)).unsigned = true;
                        else if (typeof object.enrSeq === "string")
                            message.enrSeq = parseInt(object.enrSeq, 10);
                        else if (typeof object.enrSeq === "number")
                            message.enrSeq = object.enrSeq;
                        else if (typeof object.enrSeq === "object")
                            message.enrSeq = new $util.LongBits(object.enrSeq.low >>> 0, object.enrSeq.high >>> 0).toNumber(true);
                    return message;
                };

                /**
                 * Creates a plain object from a Record message. Also converts values to other types if specified.
                 * @function toObject
                 * @memberof tracing.Log.SendHandshakeMessage.Record
                 * @static
                 * @param {tracing.Log.SendHandshakeMessage.Record} message Record
                 * @param {$protobuf.IConversionOptions} [options] Conversion options
                 * @returns {Object.<string,*>} Plain object
                 */
                Record.toObject = function toObject(message, options) {
                    if (!options)
                        options = {};
                    var object = {};
                    if (options.defaults)
                        if ($util.Long) {
                            var long = new $util.Long(0, 0, true);
                            object.enrSeq = options.longs === String ? long.toString() : options.longs === Number ? long.toNumber() : long;
                        } else
                            object.enrSeq = options.longs === String ? "0" : 0;
                    if (message.enrSeq != null && message.hasOwnProperty("enrSeq"))
                        if (typeof message.enrSeq === "number")
                            object.enrSeq = options.longs === String ? String(message.enrSeq) : message.enrSeq;
                        else
                            object.enrSeq = options.longs === String ? $util.Long.prototype.toString.call(message.enrSeq) : options.longs === Number ? new $util.LongBits(message.enrSeq.low >>> 0, message.enrSeq.high >>> 0).toNumber(true) : message.enrSeq;
                    return object;
                };

                /**
                 * Converts this Record to JSON.
                 * @function toJSON
                 * @memberof tracing.Log.SendHandshakeMessage.Record
                 * @instance
                 * @returns {Object.<string,*>} JSON object
                 */
                Record.prototype.toJSON = function toJSON() {
                    return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
                };

                return Record;
            })();

            return SendHandshakeMessage;
        })();

        return Log;
    })();

    tracing.Random = (function() {

        /**
         * Properties of a Random.
         * @memberof tracing
         * @interface IRandom
         */

        /**
         * Constructs a new Random.
         * @memberof tracing
         * @classdesc Represents a Random.
         * @implements IRandom
         * @constructor
         * @param {tracing.IRandom=} [properties] Properties to set
         */
        function Random(properties) {
            if (properties)
                for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                    if (properties[keys[i]] != null)
                        this[keys[i]] = properties[keys[i]];
        }

        /**
         * Creates a new Random instance using the specified properties.
         * @function create
         * @memberof tracing.Random
         * @static
         * @param {tracing.IRandom=} [properties] Properties to set
         * @returns {tracing.Random} Random instance
         */
        Random.create = function create(properties) {
            return new Random(properties);
        };

        /**
         * Encodes the specified Random message. Does not implicitly {@link tracing.Random.verify|verify} messages.
         * @function encode
         * @memberof tracing.Random
         * @static
         * @param {tracing.IRandom} message Random message or plain object to encode
         * @param {$protobuf.Writer} [writer] Writer to encode to
         * @returns {$protobuf.Writer} Writer
         */
        Random.encode = function encode(message, writer) {
            if (!writer)
                writer = $Writer.create();
            return writer;
        };

        /**
         * Encodes the specified Random message, length delimited. Does not implicitly {@link tracing.Random.verify|verify} messages.
         * @function encodeDelimited
         * @memberof tracing.Random
         * @static
         * @param {tracing.IRandom} message Random message or plain object to encode
         * @param {$protobuf.Writer} [writer] Writer to encode to
         * @returns {$protobuf.Writer} Writer
         */
        Random.encodeDelimited = function encodeDelimited(message, writer) {
            return this.encode(message, writer).ldelim();
        };

        /**
         * Decodes a Random message from the specified reader or buffer.
         * @function decode
         * @memberof tracing.Random
         * @static
         * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
         * @param {number} [length] Message length if known beforehand
         * @returns {tracing.Random} Random
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        Random.decode = function decode(reader, length) {
            if (!(reader instanceof $Reader))
                reader = $Reader.create(reader);
            var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.Random();
            while (reader.pos < end) {
                var tag = reader.uint32();
                switch (tag >>> 3) {
                default:
                    reader.skipType(tag & 7);
                    break;
                }
            }
            return message;
        };

        /**
         * Decodes a Random message from the specified reader or buffer, length delimited.
         * @function decodeDelimited
         * @memberof tracing.Random
         * @static
         * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
         * @returns {tracing.Random} Random
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        Random.decodeDelimited = function decodeDelimited(reader) {
            if (!(reader instanceof $Reader))
                reader = new $Reader(reader);
            return this.decode(reader, reader.uint32());
        };

        /**
         * Verifies a Random message.
         * @function verify
         * @memberof tracing.Random
         * @static
         * @param {Object.<string,*>} message Plain object to verify
         * @returns {string|null} `null` if valid, otherwise the reason why it is not
         */
        Random.verify = function verify(message) {
            if (typeof message !== "object" || message === null)
                return "object expected";
            return null;
        };

        /**
         * Creates a Random message from a plain object. Also converts values to their respective internal types.
         * @function fromObject
         * @memberof tracing.Random
         * @static
         * @param {Object.<string,*>} object Plain object
         * @returns {tracing.Random} Random
         */
        Random.fromObject = function fromObject(object) {
            if (object instanceof $root.tracing.Random)
                return object;
            return new $root.tracing.Random();
        };

        /**
         * Creates a plain object from a Random message. Also converts values to other types if specified.
         * @function toObject
         * @memberof tracing.Random
         * @static
         * @param {tracing.Random} message Random
         * @param {$protobuf.IConversionOptions} [options] Conversion options
         * @returns {Object.<string,*>} Plain object
         */
        Random.toObject = function toObject() {
            return {};
        };

        /**
         * Converts this Random to JSON.
         * @function toJSON
         * @memberof tracing.Random
         * @instance
         * @returns {Object.<string,*>} JSON object
         */
        Random.prototype.toJSON = function toJSON() {
            return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
        };

        return Random;
    })();

    tracing.Ping = (function() {

        /**
         * Properties of a Ping.
         * @memberof tracing
         * @interface IPing
         * @property {string|null} [requestId] Ping requestId
         * @property {number|Long|null} [enrSeq] Ping enrSeq
         */

        /**
         * Constructs a new Ping.
         * @memberof tracing
         * @classdesc Represents a Ping.
         * @implements IPing
         * @constructor
         * @param {tracing.IPing=} [properties] Properties to set
         */
        function Ping(properties) {
            if (properties)
                for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                    if (properties[keys[i]] != null)
                        this[keys[i]] = properties[keys[i]];
        }

        /**
         * Ping requestId.
         * @member {string} requestId
         * @memberof tracing.Ping
         * @instance
         */
        Ping.prototype.requestId = "";

        /**
         * Ping enrSeq.
         * @member {number|Long} enrSeq
         * @memberof tracing.Ping
         * @instance
         */
        Ping.prototype.enrSeq = $util.Long ? $util.Long.fromBits(0,0,true) : 0;

        /**
         * Creates a new Ping instance using the specified properties.
         * @function create
         * @memberof tracing.Ping
         * @static
         * @param {tracing.IPing=} [properties] Properties to set
         * @returns {tracing.Ping} Ping instance
         */
        Ping.create = function create(properties) {
            return new Ping(properties);
        };

        /**
         * Encodes the specified Ping message. Does not implicitly {@link tracing.Ping.verify|verify} messages.
         * @function encode
         * @memberof tracing.Ping
         * @static
         * @param {tracing.IPing} message Ping message or plain object to encode
         * @param {$protobuf.Writer} [writer] Writer to encode to
         * @returns {$protobuf.Writer} Writer
         */
        Ping.encode = function encode(message, writer) {
            if (!writer)
                writer = $Writer.create();
            if (message.requestId != null && Object.hasOwnProperty.call(message, "requestId"))
                writer.uint32(/* id 1, wireType 2 =*/10).string(message.requestId);
            if (message.enrSeq != null && Object.hasOwnProperty.call(message, "enrSeq"))
                writer.uint32(/* id 2, wireType 0 =*/16).uint64(message.enrSeq);
            return writer;
        };

        /**
         * Encodes the specified Ping message, length delimited. Does not implicitly {@link tracing.Ping.verify|verify} messages.
         * @function encodeDelimited
         * @memberof tracing.Ping
         * @static
         * @param {tracing.IPing} message Ping message or plain object to encode
         * @param {$protobuf.Writer} [writer] Writer to encode to
         * @returns {$protobuf.Writer} Writer
         */
        Ping.encodeDelimited = function encodeDelimited(message, writer) {
            return this.encode(message, writer).ldelim();
        };

        /**
         * Decodes a Ping message from the specified reader or buffer.
         * @function decode
         * @memberof tracing.Ping
         * @static
         * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
         * @param {number} [length] Message length if known beforehand
         * @returns {tracing.Ping} Ping
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        Ping.decode = function decode(reader, length) {
            if (!(reader instanceof $Reader))
                reader = $Reader.create(reader);
            var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.Ping();
            while (reader.pos < end) {
                var tag = reader.uint32();
                switch (tag >>> 3) {
                case 1:
                    message.requestId = reader.string();
                    break;
                case 2:
                    message.enrSeq = reader.uint64();
                    break;
                default:
                    reader.skipType(tag & 7);
                    break;
                }
            }
            return message;
        };

        /**
         * Decodes a Ping message from the specified reader or buffer, length delimited.
         * @function decodeDelimited
         * @memberof tracing.Ping
         * @static
         * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
         * @returns {tracing.Ping} Ping
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        Ping.decodeDelimited = function decodeDelimited(reader) {
            if (!(reader instanceof $Reader))
                reader = new $Reader(reader);
            return this.decode(reader, reader.uint32());
        };

        /**
         * Verifies a Ping message.
         * @function verify
         * @memberof tracing.Ping
         * @static
         * @param {Object.<string,*>} message Plain object to verify
         * @returns {string|null} `null` if valid, otherwise the reason why it is not
         */
        Ping.verify = function verify(message) {
            if (typeof message !== "object" || message === null)
                return "object expected";
            if (message.requestId != null && message.hasOwnProperty("requestId"))
                if (!$util.isString(message.requestId))
                    return "requestId: string expected";
            if (message.enrSeq != null && message.hasOwnProperty("enrSeq"))
                if (!$util.isInteger(message.enrSeq) && !(message.enrSeq && $util.isInteger(message.enrSeq.low) && $util.isInteger(message.enrSeq.high)))
                    return "enrSeq: integer|Long expected";
            return null;
        };

        /**
         * Creates a Ping message from a plain object. Also converts values to their respective internal types.
         * @function fromObject
         * @memberof tracing.Ping
         * @static
         * @param {Object.<string,*>} object Plain object
         * @returns {tracing.Ping} Ping
         */
        Ping.fromObject = function fromObject(object) {
            if (object instanceof $root.tracing.Ping)
                return object;
            var message = new $root.tracing.Ping();
            if (object.requestId != null)
                message.requestId = String(object.requestId);
            if (object.enrSeq != null)
                if ($util.Long)
                    (message.enrSeq = $util.Long.fromValue(object.enrSeq)).unsigned = true;
                else if (typeof object.enrSeq === "string")
                    message.enrSeq = parseInt(object.enrSeq, 10);
                else if (typeof object.enrSeq === "number")
                    message.enrSeq = object.enrSeq;
                else if (typeof object.enrSeq === "object")
                    message.enrSeq = new $util.LongBits(object.enrSeq.low >>> 0, object.enrSeq.high >>> 0).toNumber(true);
            return message;
        };

        /**
         * Creates a plain object from a Ping message. Also converts values to other types if specified.
         * @function toObject
         * @memberof tracing.Ping
         * @static
         * @param {tracing.Ping} message Ping
         * @param {$protobuf.IConversionOptions} [options] Conversion options
         * @returns {Object.<string,*>} Plain object
         */
        Ping.toObject = function toObject(message, options) {
            if (!options)
                options = {};
            var object = {};
            if (options.defaults) {
                object.requestId = "";
                if ($util.Long) {
                    var long = new $util.Long(0, 0, true);
                    object.enrSeq = options.longs === String ? long.toString() : options.longs === Number ? long.toNumber() : long;
                } else
                    object.enrSeq = options.longs === String ? "0" : 0;
            }
            if (message.requestId != null && message.hasOwnProperty("requestId"))
                object.requestId = message.requestId;
            if (message.enrSeq != null && message.hasOwnProperty("enrSeq"))
                if (typeof message.enrSeq === "number")
                    object.enrSeq = options.longs === String ? String(message.enrSeq) : message.enrSeq;
                else
                    object.enrSeq = options.longs === String ? $util.Long.prototype.toString.call(message.enrSeq) : options.longs === Number ? new $util.LongBits(message.enrSeq.low >>> 0, message.enrSeq.high >>> 0).toNumber(true) : message.enrSeq;
            return object;
        };

        /**
         * Converts this Ping to JSON.
         * @function toJSON
         * @memberof tracing.Ping
         * @instance
         * @returns {Object.<string,*>} JSON object
         */
        Ping.prototype.toJSON = function toJSON() {
            return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
        };

        return Ping;
    })();

    tracing.Pong = (function() {

        /**
         * Properties of a Pong.
         * @memberof tracing
         * @interface IPong
         * @property {string|null} [requestId] Pong requestId
         * @property {number|Long|null} [enrSeq] Pong enrSeq
         * @property {string|null} [recipientIp] Pong recipientIp
         * @property {number|null} [recipientPort] Pong recipientPort
         */

        /**
         * Constructs a new Pong.
         * @memberof tracing
         * @classdesc Represents a Pong.
         * @implements IPong
         * @constructor
         * @param {tracing.IPong=} [properties] Properties to set
         */
        function Pong(properties) {
            if (properties)
                for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                    if (properties[keys[i]] != null)
                        this[keys[i]] = properties[keys[i]];
        }

        /**
         * Pong requestId.
         * @member {string} requestId
         * @memberof tracing.Pong
         * @instance
         */
        Pong.prototype.requestId = "";

        /**
         * Pong enrSeq.
         * @member {number|Long} enrSeq
         * @memberof tracing.Pong
         * @instance
         */
        Pong.prototype.enrSeq = $util.Long ? $util.Long.fromBits(0,0,true) : 0;

        /**
         * Pong recipientIp.
         * @member {string} recipientIp
         * @memberof tracing.Pong
         * @instance
         */
        Pong.prototype.recipientIp = "";

        /**
         * Pong recipientPort.
         * @member {number} recipientPort
         * @memberof tracing.Pong
         * @instance
         */
        Pong.prototype.recipientPort = 0;

        /**
         * Creates a new Pong instance using the specified properties.
         * @function create
         * @memberof tracing.Pong
         * @static
         * @param {tracing.IPong=} [properties] Properties to set
         * @returns {tracing.Pong} Pong instance
         */
        Pong.create = function create(properties) {
            return new Pong(properties);
        };

        /**
         * Encodes the specified Pong message. Does not implicitly {@link tracing.Pong.verify|verify} messages.
         * @function encode
         * @memberof tracing.Pong
         * @static
         * @param {tracing.IPong} message Pong message or plain object to encode
         * @param {$protobuf.Writer} [writer] Writer to encode to
         * @returns {$protobuf.Writer} Writer
         */
        Pong.encode = function encode(message, writer) {
            if (!writer)
                writer = $Writer.create();
            if (message.requestId != null && Object.hasOwnProperty.call(message, "requestId"))
                writer.uint32(/* id 1, wireType 2 =*/10).string(message.requestId);
            if (message.enrSeq != null && Object.hasOwnProperty.call(message, "enrSeq"))
                writer.uint32(/* id 2, wireType 0 =*/16).uint64(message.enrSeq);
            if (message.recipientIp != null && Object.hasOwnProperty.call(message, "recipientIp"))
                writer.uint32(/* id 3, wireType 2 =*/26).string(message.recipientIp);
            if (message.recipientPort != null && Object.hasOwnProperty.call(message, "recipientPort"))
                writer.uint32(/* id 4, wireType 0 =*/32).uint32(message.recipientPort);
            return writer;
        };

        /**
         * Encodes the specified Pong message, length delimited. Does not implicitly {@link tracing.Pong.verify|verify} messages.
         * @function encodeDelimited
         * @memberof tracing.Pong
         * @static
         * @param {tracing.IPong} message Pong message or plain object to encode
         * @param {$protobuf.Writer} [writer] Writer to encode to
         * @returns {$protobuf.Writer} Writer
         */
        Pong.encodeDelimited = function encodeDelimited(message, writer) {
            return this.encode(message, writer).ldelim();
        };

        /**
         * Decodes a Pong message from the specified reader or buffer.
         * @function decode
         * @memberof tracing.Pong
         * @static
         * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
         * @param {number} [length] Message length if known beforehand
         * @returns {tracing.Pong} Pong
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        Pong.decode = function decode(reader, length) {
            if (!(reader instanceof $Reader))
                reader = $Reader.create(reader);
            var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.Pong();
            while (reader.pos < end) {
                var tag = reader.uint32();
                switch (tag >>> 3) {
                case 1:
                    message.requestId = reader.string();
                    break;
                case 2:
                    message.enrSeq = reader.uint64();
                    break;
                case 3:
                    message.recipientIp = reader.string();
                    break;
                case 4:
                    message.recipientPort = reader.uint32();
                    break;
                default:
                    reader.skipType(tag & 7);
                    break;
                }
            }
            return message;
        };

        /**
         * Decodes a Pong message from the specified reader or buffer, length delimited.
         * @function decodeDelimited
         * @memberof tracing.Pong
         * @static
         * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
         * @returns {tracing.Pong} Pong
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        Pong.decodeDelimited = function decodeDelimited(reader) {
            if (!(reader instanceof $Reader))
                reader = new $Reader(reader);
            return this.decode(reader, reader.uint32());
        };

        /**
         * Verifies a Pong message.
         * @function verify
         * @memberof tracing.Pong
         * @static
         * @param {Object.<string,*>} message Plain object to verify
         * @returns {string|null} `null` if valid, otherwise the reason why it is not
         */
        Pong.verify = function verify(message) {
            if (typeof message !== "object" || message === null)
                return "object expected";
            if (message.requestId != null && message.hasOwnProperty("requestId"))
                if (!$util.isString(message.requestId))
                    return "requestId: string expected";
            if (message.enrSeq != null && message.hasOwnProperty("enrSeq"))
                if (!$util.isInteger(message.enrSeq) && !(message.enrSeq && $util.isInteger(message.enrSeq.low) && $util.isInteger(message.enrSeq.high)))
                    return "enrSeq: integer|Long expected";
            if (message.recipientIp != null && message.hasOwnProperty("recipientIp"))
                if (!$util.isString(message.recipientIp))
                    return "recipientIp: string expected";
            if (message.recipientPort != null && message.hasOwnProperty("recipientPort"))
                if (!$util.isInteger(message.recipientPort))
                    return "recipientPort: integer expected";
            return null;
        };

        /**
         * Creates a Pong message from a plain object. Also converts values to their respective internal types.
         * @function fromObject
         * @memberof tracing.Pong
         * @static
         * @param {Object.<string,*>} object Plain object
         * @returns {tracing.Pong} Pong
         */
        Pong.fromObject = function fromObject(object) {
            if (object instanceof $root.tracing.Pong)
                return object;
            var message = new $root.tracing.Pong();
            if (object.requestId != null)
                message.requestId = String(object.requestId);
            if (object.enrSeq != null)
                if ($util.Long)
                    (message.enrSeq = $util.Long.fromValue(object.enrSeq)).unsigned = true;
                else if (typeof object.enrSeq === "string")
                    message.enrSeq = parseInt(object.enrSeq, 10);
                else if (typeof object.enrSeq === "number")
                    message.enrSeq = object.enrSeq;
                else if (typeof object.enrSeq === "object")
                    message.enrSeq = new $util.LongBits(object.enrSeq.low >>> 0, object.enrSeq.high >>> 0).toNumber(true);
            if (object.recipientIp != null)
                message.recipientIp = String(object.recipientIp);
            if (object.recipientPort != null)
                message.recipientPort = object.recipientPort >>> 0;
            return message;
        };

        /**
         * Creates a plain object from a Pong message. Also converts values to other types if specified.
         * @function toObject
         * @memberof tracing.Pong
         * @static
         * @param {tracing.Pong} message Pong
         * @param {$protobuf.IConversionOptions} [options] Conversion options
         * @returns {Object.<string,*>} Plain object
         */
        Pong.toObject = function toObject(message, options) {
            if (!options)
                options = {};
            var object = {};
            if (options.defaults) {
                object.requestId = "";
                if ($util.Long) {
                    var long = new $util.Long(0, 0, true);
                    object.enrSeq = options.longs === String ? long.toString() : options.longs === Number ? long.toNumber() : long;
                } else
                    object.enrSeq = options.longs === String ? "0" : 0;
                object.recipientIp = "";
                object.recipientPort = 0;
            }
            if (message.requestId != null && message.hasOwnProperty("requestId"))
                object.requestId = message.requestId;
            if (message.enrSeq != null && message.hasOwnProperty("enrSeq"))
                if (typeof message.enrSeq === "number")
                    object.enrSeq = options.longs === String ? String(message.enrSeq) : message.enrSeq;
                else
                    object.enrSeq = options.longs === String ? $util.Long.prototype.toString.call(message.enrSeq) : options.longs === Number ? new $util.LongBits(message.enrSeq.low >>> 0, message.enrSeq.high >>> 0).toNumber(true) : message.enrSeq;
            if (message.recipientIp != null && message.hasOwnProperty("recipientIp"))
                object.recipientIp = message.recipientIp;
            if (message.recipientPort != null && message.hasOwnProperty("recipientPort"))
                object.recipientPort = message.recipientPort;
            return object;
        };

        /**
         * Converts this Pong to JSON.
         * @function toJSON
         * @memberof tracing.Pong
         * @instance
         * @returns {Object.<string,*>} JSON object
         */
        Pong.prototype.toJSON = function toJSON() {
            return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
        };

        return Pong;
    })();

    tracing.FindNode = (function() {

        /**
         * Properties of a FindNode.
         * @memberof tracing
         * @interface IFindNode
         * @property {string|null} [requestId] FindNode requestId
         * @property {Array.<number|Long>|null} [distances] FindNode distances
         */

        /**
         * Constructs a new FindNode.
         * @memberof tracing
         * @classdesc Represents a FindNode.
         * @implements IFindNode
         * @constructor
         * @param {tracing.IFindNode=} [properties] Properties to set
         */
        function FindNode(properties) {
            this.distances = [];
            if (properties)
                for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                    if (properties[keys[i]] != null)
                        this[keys[i]] = properties[keys[i]];
        }

        /**
         * FindNode requestId.
         * @member {string} requestId
         * @memberof tracing.FindNode
         * @instance
         */
        FindNode.prototype.requestId = "";

        /**
         * FindNode distances.
         * @member {Array.<number|Long>} distances
         * @memberof tracing.FindNode
         * @instance
         */
        FindNode.prototype.distances = $util.emptyArray;

        /**
         * Creates a new FindNode instance using the specified properties.
         * @function create
         * @memberof tracing.FindNode
         * @static
         * @param {tracing.IFindNode=} [properties] Properties to set
         * @returns {tracing.FindNode} FindNode instance
         */
        FindNode.create = function create(properties) {
            return new FindNode(properties);
        };

        /**
         * Encodes the specified FindNode message. Does not implicitly {@link tracing.FindNode.verify|verify} messages.
         * @function encode
         * @memberof tracing.FindNode
         * @static
         * @param {tracing.IFindNode} message FindNode message or plain object to encode
         * @param {$protobuf.Writer} [writer] Writer to encode to
         * @returns {$protobuf.Writer} Writer
         */
        FindNode.encode = function encode(message, writer) {
            if (!writer)
                writer = $Writer.create();
            if (message.requestId != null && Object.hasOwnProperty.call(message, "requestId"))
                writer.uint32(/* id 1, wireType 2 =*/10).string(message.requestId);
            if (message.distances != null && message.distances.length) {
                writer.uint32(/* id 2, wireType 2 =*/18).fork();
                for (var i = 0; i < message.distances.length; ++i)
                    writer.uint64(message.distances[i]);
                writer.ldelim();
            }
            return writer;
        };

        /**
         * Encodes the specified FindNode message, length delimited. Does not implicitly {@link tracing.FindNode.verify|verify} messages.
         * @function encodeDelimited
         * @memberof tracing.FindNode
         * @static
         * @param {tracing.IFindNode} message FindNode message or plain object to encode
         * @param {$protobuf.Writer} [writer] Writer to encode to
         * @returns {$protobuf.Writer} Writer
         */
        FindNode.encodeDelimited = function encodeDelimited(message, writer) {
            return this.encode(message, writer).ldelim();
        };

        /**
         * Decodes a FindNode message from the specified reader or buffer.
         * @function decode
         * @memberof tracing.FindNode
         * @static
         * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
         * @param {number} [length] Message length if known beforehand
         * @returns {tracing.FindNode} FindNode
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        FindNode.decode = function decode(reader, length) {
            if (!(reader instanceof $Reader))
                reader = $Reader.create(reader);
            var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.FindNode();
            while (reader.pos < end) {
                var tag = reader.uint32();
                switch (tag >>> 3) {
                case 1:
                    message.requestId = reader.string();
                    break;
                case 2:
                    if (!(message.distances && message.distances.length))
                        message.distances = [];
                    if ((tag & 7) === 2) {
                        var end2 = reader.uint32() + reader.pos;
                        while (reader.pos < end2)
                            message.distances.push(reader.uint64());
                    } else
                        message.distances.push(reader.uint64());
                    break;
                default:
                    reader.skipType(tag & 7);
                    break;
                }
            }
            return message;
        };

        /**
         * Decodes a FindNode message from the specified reader or buffer, length delimited.
         * @function decodeDelimited
         * @memberof tracing.FindNode
         * @static
         * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
         * @returns {tracing.FindNode} FindNode
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        FindNode.decodeDelimited = function decodeDelimited(reader) {
            if (!(reader instanceof $Reader))
                reader = new $Reader(reader);
            return this.decode(reader, reader.uint32());
        };

        /**
         * Verifies a FindNode message.
         * @function verify
         * @memberof tracing.FindNode
         * @static
         * @param {Object.<string,*>} message Plain object to verify
         * @returns {string|null} `null` if valid, otherwise the reason why it is not
         */
        FindNode.verify = function verify(message) {
            if (typeof message !== "object" || message === null)
                return "object expected";
            if (message.requestId != null && message.hasOwnProperty("requestId"))
                if (!$util.isString(message.requestId))
                    return "requestId: string expected";
            if (message.distances != null && message.hasOwnProperty("distances")) {
                if (!Array.isArray(message.distances))
                    return "distances: array expected";
                for (var i = 0; i < message.distances.length; ++i)
                    if (!$util.isInteger(message.distances[i]) && !(message.distances[i] && $util.isInteger(message.distances[i].low) && $util.isInteger(message.distances[i].high)))
                        return "distances: integer|Long[] expected";
            }
            return null;
        };

        /**
         * Creates a FindNode message from a plain object. Also converts values to their respective internal types.
         * @function fromObject
         * @memberof tracing.FindNode
         * @static
         * @param {Object.<string,*>} object Plain object
         * @returns {tracing.FindNode} FindNode
         */
        FindNode.fromObject = function fromObject(object) {
            if (object instanceof $root.tracing.FindNode)
                return object;
            var message = new $root.tracing.FindNode();
            if (object.requestId != null)
                message.requestId = String(object.requestId);
            if (object.distances) {
                if (!Array.isArray(object.distances))
                    throw TypeError(".tracing.FindNode.distances: array expected");
                message.distances = [];
                for (var i = 0; i < object.distances.length; ++i)
                    if ($util.Long)
                        (message.distances[i] = $util.Long.fromValue(object.distances[i])).unsigned = true;
                    else if (typeof object.distances[i] === "string")
                        message.distances[i] = parseInt(object.distances[i], 10);
                    else if (typeof object.distances[i] === "number")
                        message.distances[i] = object.distances[i];
                    else if (typeof object.distances[i] === "object")
                        message.distances[i] = new $util.LongBits(object.distances[i].low >>> 0, object.distances[i].high >>> 0).toNumber(true);
            }
            return message;
        };

        /**
         * Creates a plain object from a FindNode message. Also converts values to other types if specified.
         * @function toObject
         * @memberof tracing.FindNode
         * @static
         * @param {tracing.FindNode} message FindNode
         * @param {$protobuf.IConversionOptions} [options] Conversion options
         * @returns {Object.<string,*>} Plain object
         */
        FindNode.toObject = function toObject(message, options) {
            if (!options)
                options = {};
            var object = {};
            if (options.arrays || options.defaults)
                object.distances = [];
            if (options.defaults)
                object.requestId = "";
            if (message.requestId != null && message.hasOwnProperty("requestId"))
                object.requestId = message.requestId;
            if (message.distances && message.distances.length) {
                object.distances = [];
                for (var j = 0; j < message.distances.length; ++j)
                    if (typeof message.distances[j] === "number")
                        object.distances[j] = options.longs === String ? String(message.distances[j]) : message.distances[j];
                    else
                        object.distances[j] = options.longs === String ? $util.Long.prototype.toString.call(message.distances[j]) : options.longs === Number ? new $util.LongBits(message.distances[j].low >>> 0, message.distances[j].high >>> 0).toNumber(true) : message.distances[j];
            }
            return object;
        };

        /**
         * Converts this FindNode to JSON.
         * @function toJSON
         * @memberof tracing.FindNode
         * @instance
         * @returns {Object.<string,*>} JSON object
         */
        FindNode.prototype.toJSON = function toJSON() {
            return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
        };

        return FindNode;
    })();

    tracing.Nodes = (function() {

        /**
         * Properties of a Nodes.
         * @memberof tracing
         * @interface INodes
         * @property {string|null} [requestId] Nodes requestId
         * @property {number|Long|null} [total] Nodes total
         * @property {Array.<string>|null} [nodes] Nodes nodes
         */

        /**
         * Constructs a new Nodes.
         * @memberof tracing
         * @classdesc Represents a Nodes.
         * @implements INodes
         * @constructor
         * @param {tracing.INodes=} [properties] Properties to set
         */
        function Nodes(properties) {
            this.nodes = [];
            if (properties)
                for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                    if (properties[keys[i]] != null)
                        this[keys[i]] = properties[keys[i]];
        }

        /**
         * Nodes requestId.
         * @member {string} requestId
         * @memberof tracing.Nodes
         * @instance
         */
        Nodes.prototype.requestId = "";

        /**
         * Nodes total.
         * @member {number|Long} total
         * @memberof tracing.Nodes
         * @instance
         */
        Nodes.prototype.total = $util.Long ? $util.Long.fromBits(0,0,true) : 0;

        /**
         * Nodes nodes.
         * @member {Array.<string>} nodes
         * @memberof tracing.Nodes
         * @instance
         */
        Nodes.prototype.nodes = $util.emptyArray;

        /**
         * Creates a new Nodes instance using the specified properties.
         * @function create
         * @memberof tracing.Nodes
         * @static
         * @param {tracing.INodes=} [properties] Properties to set
         * @returns {tracing.Nodes} Nodes instance
         */
        Nodes.create = function create(properties) {
            return new Nodes(properties);
        };

        /**
         * Encodes the specified Nodes message. Does not implicitly {@link tracing.Nodes.verify|verify} messages.
         * @function encode
         * @memberof tracing.Nodes
         * @static
         * @param {tracing.INodes} message Nodes message or plain object to encode
         * @param {$protobuf.Writer} [writer] Writer to encode to
         * @returns {$protobuf.Writer} Writer
         */
        Nodes.encode = function encode(message, writer) {
            if (!writer)
                writer = $Writer.create();
            if (message.requestId != null && Object.hasOwnProperty.call(message, "requestId"))
                writer.uint32(/* id 1, wireType 2 =*/10).string(message.requestId);
            if (message.total != null && Object.hasOwnProperty.call(message, "total"))
                writer.uint32(/* id 2, wireType 0 =*/16).uint64(message.total);
            if (message.nodes != null && message.nodes.length)
                for (var i = 0; i < message.nodes.length; ++i)
                    writer.uint32(/* id 3, wireType 2 =*/26).string(message.nodes[i]);
            return writer;
        };

        /**
         * Encodes the specified Nodes message, length delimited. Does not implicitly {@link tracing.Nodes.verify|verify} messages.
         * @function encodeDelimited
         * @memberof tracing.Nodes
         * @static
         * @param {tracing.INodes} message Nodes message or plain object to encode
         * @param {$protobuf.Writer} [writer] Writer to encode to
         * @returns {$protobuf.Writer} Writer
         */
        Nodes.encodeDelimited = function encodeDelimited(message, writer) {
            return this.encode(message, writer).ldelim();
        };

        /**
         * Decodes a Nodes message from the specified reader or buffer.
         * @function decode
         * @memberof tracing.Nodes
         * @static
         * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
         * @param {number} [length] Message length if known beforehand
         * @returns {tracing.Nodes} Nodes
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        Nodes.decode = function decode(reader, length) {
            if (!(reader instanceof $Reader))
                reader = $Reader.create(reader);
            var end = length === undefined ? reader.len : reader.pos + length, message = new $root.tracing.Nodes();
            while (reader.pos < end) {
                var tag = reader.uint32();
                switch (tag >>> 3) {
                case 1:
                    message.requestId = reader.string();
                    break;
                case 2:
                    message.total = reader.uint64();
                    break;
                case 3:
                    if (!(message.nodes && message.nodes.length))
                        message.nodes = [];
                    message.nodes.push(reader.string());
                    break;
                default:
                    reader.skipType(tag & 7);
                    break;
                }
            }
            return message;
        };

        /**
         * Decodes a Nodes message from the specified reader or buffer, length delimited.
         * @function decodeDelimited
         * @memberof tracing.Nodes
         * @static
         * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
         * @returns {tracing.Nodes} Nodes
         * @throws {Error} If the payload is not a reader or valid buffer
         * @throws {$protobuf.util.ProtocolError} If required fields are missing
         */
        Nodes.decodeDelimited = function decodeDelimited(reader) {
            if (!(reader instanceof $Reader))
                reader = new $Reader(reader);
            return this.decode(reader, reader.uint32());
        };

        /**
         * Verifies a Nodes message.
         * @function verify
         * @memberof tracing.Nodes
         * @static
         * @param {Object.<string,*>} message Plain object to verify
         * @returns {string|null} `null` if valid, otherwise the reason why it is not
         */
        Nodes.verify = function verify(message) {
            if (typeof message !== "object" || message === null)
                return "object expected";
            if (message.requestId != null && message.hasOwnProperty("requestId"))
                if (!$util.isString(message.requestId))
                    return "requestId: string expected";
            if (message.total != null && message.hasOwnProperty("total"))
                if (!$util.isInteger(message.total) && !(message.total && $util.isInteger(message.total.low) && $util.isInteger(message.total.high)))
                    return "total: integer|Long expected";
            if (message.nodes != null && message.hasOwnProperty("nodes")) {
                if (!Array.isArray(message.nodes))
                    return "nodes: array expected";
                for (var i = 0; i < message.nodes.length; ++i)
                    if (!$util.isString(message.nodes[i]))
                        return "nodes: string[] expected";
            }
            return null;
        };

        /**
         * Creates a Nodes message from a plain object. Also converts values to their respective internal types.
         * @function fromObject
         * @memberof tracing.Nodes
         * @static
         * @param {Object.<string,*>} object Plain object
         * @returns {tracing.Nodes} Nodes
         */
        Nodes.fromObject = function fromObject(object) {
            if (object instanceof $root.tracing.Nodes)
                return object;
            var message = new $root.tracing.Nodes();
            if (object.requestId != null)
                message.requestId = String(object.requestId);
            if (object.total != null)
                if ($util.Long)
                    (message.total = $util.Long.fromValue(object.total)).unsigned = true;
                else if (typeof object.total === "string")
                    message.total = parseInt(object.total, 10);
                else if (typeof object.total === "number")
                    message.total = object.total;
                else if (typeof object.total === "object")
                    message.total = new $util.LongBits(object.total.low >>> 0, object.total.high >>> 0).toNumber(true);
            if (object.nodes) {
                if (!Array.isArray(object.nodes))
                    throw TypeError(".tracing.Nodes.nodes: array expected");
                message.nodes = [];
                for (var i = 0; i < object.nodes.length; ++i)
                    message.nodes[i] = String(object.nodes[i]);
            }
            return message;
        };

        /**
         * Creates a plain object from a Nodes message. Also converts values to other types if specified.
         * @function toObject
         * @memberof tracing.Nodes
         * @static
         * @param {tracing.Nodes} message Nodes
         * @param {$protobuf.IConversionOptions} [options] Conversion options
         * @returns {Object.<string,*>} Plain object
         */
        Nodes.toObject = function toObject(message, options) {
            if (!options)
                options = {};
            var object = {};
            if (options.arrays || options.defaults)
                object.nodes = [];
            if (options.defaults) {
                object.requestId = "";
                if ($util.Long) {
                    var long = new $util.Long(0, 0, true);
                    object.total = options.longs === String ? long.toString() : options.longs === Number ? long.toNumber() : long;
                } else
                    object.total = options.longs === String ? "0" : 0;
            }
            if (message.requestId != null && message.hasOwnProperty("requestId"))
                object.requestId = message.requestId;
            if (message.total != null && message.hasOwnProperty("total"))
                if (typeof message.total === "number")
                    object.total = options.longs === String ? String(message.total) : message.total;
                else
                    object.total = options.longs === String ? $util.Long.prototype.toString.call(message.total) : options.longs === Number ? new $util.LongBits(message.total.low >>> 0, message.total.high >>> 0).toNumber(true) : message.total;
            if (message.nodes && message.nodes.length) {
                object.nodes = [];
                for (var j = 0; j < message.nodes.length; ++j)
                    object.nodes[j] = message.nodes[j];
            }
            return object;
        };

        /**
         * Converts this Nodes to JSON.
         * @function toJSON
         * @memberof tracing.Nodes
         * @instance
         * @returns {Object.<string,*>} JSON object
         */
        Nodes.prototype.toJSON = function toJSON() {
            return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
        };

        return Nodes;
    })();

    return tracing;
})();

$root.google = (function() {

    /**
     * Namespace google.
     * @exports google
     * @namespace
     */
    var google = {};

    google.protobuf = (function() {

        /**
         * Namespace protobuf.
         * @memberof google
         * @namespace
         */
        var protobuf = {};

        protobuf.Timestamp = (function() {

            /**
             * Properties of a Timestamp.
             * @memberof google.protobuf
             * @interface ITimestamp
             * @property {number|Long|null} [seconds] Timestamp seconds
             * @property {number|null} [nanos] Timestamp nanos
             */

            /**
             * Constructs a new Timestamp.
             * @memberof google.protobuf
             * @classdesc Represents a Timestamp.
             * @implements ITimestamp
             * @constructor
             * @param {google.protobuf.ITimestamp=} [properties] Properties to set
             */
            function Timestamp(properties) {
                if (properties)
                    for (var keys = Object.keys(properties), i = 0; i < keys.length; ++i)
                        if (properties[keys[i]] != null)
                            this[keys[i]] = properties[keys[i]];
            }

            /**
             * Timestamp seconds.
             * @member {number|Long} seconds
             * @memberof google.protobuf.Timestamp
             * @instance
             */
            Timestamp.prototype.seconds = $util.Long ? $util.Long.fromBits(0,0,false) : 0;

            /**
             * Timestamp nanos.
             * @member {number} nanos
             * @memberof google.protobuf.Timestamp
             * @instance
             */
            Timestamp.prototype.nanos = 0;

            /**
             * Creates a new Timestamp instance using the specified properties.
             * @function create
             * @memberof google.protobuf.Timestamp
             * @static
             * @param {google.protobuf.ITimestamp=} [properties] Properties to set
             * @returns {google.protobuf.Timestamp} Timestamp instance
             */
            Timestamp.create = function create(properties) {
                return new Timestamp(properties);
            };

            /**
             * Encodes the specified Timestamp message. Does not implicitly {@link google.protobuf.Timestamp.verify|verify} messages.
             * @function encode
             * @memberof google.protobuf.Timestamp
             * @static
             * @param {google.protobuf.ITimestamp} message Timestamp message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            Timestamp.encode = function encode(message, writer) {
                if (!writer)
                    writer = $Writer.create();
                if (message.seconds != null && Object.hasOwnProperty.call(message, "seconds"))
                    writer.uint32(/* id 1, wireType 0 =*/8).int64(message.seconds);
                if (message.nanos != null && Object.hasOwnProperty.call(message, "nanos"))
                    writer.uint32(/* id 2, wireType 0 =*/16).int32(message.nanos);
                return writer;
            };

            /**
             * Encodes the specified Timestamp message, length delimited. Does not implicitly {@link google.protobuf.Timestamp.verify|verify} messages.
             * @function encodeDelimited
             * @memberof google.protobuf.Timestamp
             * @static
             * @param {google.protobuf.ITimestamp} message Timestamp message or plain object to encode
             * @param {$protobuf.Writer} [writer] Writer to encode to
             * @returns {$protobuf.Writer} Writer
             */
            Timestamp.encodeDelimited = function encodeDelimited(message, writer) {
                return this.encode(message, writer).ldelim();
            };

            /**
             * Decodes a Timestamp message from the specified reader or buffer.
             * @function decode
             * @memberof google.protobuf.Timestamp
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @param {number} [length] Message length if known beforehand
             * @returns {google.protobuf.Timestamp} Timestamp
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            Timestamp.decode = function decode(reader, length) {
                if (!(reader instanceof $Reader))
                    reader = $Reader.create(reader);
                var end = length === undefined ? reader.len : reader.pos + length, message = new $root.google.protobuf.Timestamp();
                while (reader.pos < end) {
                    var tag = reader.uint32();
                    switch (tag >>> 3) {
                    case 1:
                        message.seconds = reader.int64();
                        break;
                    case 2:
                        message.nanos = reader.int32();
                        break;
                    default:
                        reader.skipType(tag & 7);
                        break;
                    }
                }
                return message;
            };

            /**
             * Decodes a Timestamp message from the specified reader or buffer, length delimited.
             * @function decodeDelimited
             * @memberof google.protobuf.Timestamp
             * @static
             * @param {$protobuf.Reader|Uint8Array} reader Reader or buffer to decode from
             * @returns {google.protobuf.Timestamp} Timestamp
             * @throws {Error} If the payload is not a reader or valid buffer
             * @throws {$protobuf.util.ProtocolError} If required fields are missing
             */
            Timestamp.decodeDelimited = function decodeDelimited(reader) {
                if (!(reader instanceof $Reader))
                    reader = new $Reader(reader);
                return this.decode(reader, reader.uint32());
            };

            /**
             * Verifies a Timestamp message.
             * @function verify
             * @memberof google.protobuf.Timestamp
             * @static
             * @param {Object.<string,*>} message Plain object to verify
             * @returns {string|null} `null` if valid, otherwise the reason why it is not
             */
            Timestamp.verify = function verify(message) {
                if (typeof message !== "object" || message === null)
                    return "object expected";
                if (message.seconds != null && message.hasOwnProperty("seconds"))
                    if (!$util.isInteger(message.seconds) && !(message.seconds && $util.isInteger(message.seconds.low) && $util.isInteger(message.seconds.high)))
                        return "seconds: integer|Long expected";
                if (message.nanos != null && message.hasOwnProperty("nanos"))
                    if (!$util.isInteger(message.nanos))
                        return "nanos: integer expected";
                return null;
            };

            /**
             * Creates a Timestamp message from a plain object. Also converts values to their respective internal types.
             * @function fromObject
             * @memberof google.protobuf.Timestamp
             * @static
             * @param {Object.<string,*>} object Plain object
             * @returns {google.protobuf.Timestamp} Timestamp
             */
            Timestamp.fromObject = function fromObject(object) {
                if (object instanceof $root.google.protobuf.Timestamp)
                    return object;
                var message = new $root.google.protobuf.Timestamp();
                if (object.seconds != null)
                    if ($util.Long)
                        (message.seconds = $util.Long.fromValue(object.seconds)).unsigned = false;
                    else if (typeof object.seconds === "string")
                        message.seconds = parseInt(object.seconds, 10);
                    else if (typeof object.seconds === "number")
                        message.seconds = object.seconds;
                    else if (typeof object.seconds === "object")
                        message.seconds = new $util.LongBits(object.seconds.low >>> 0, object.seconds.high >>> 0).toNumber();
                if (object.nanos != null)
                    message.nanos = object.nanos | 0;
                return message;
            };

            /**
             * Creates a plain object from a Timestamp message. Also converts values to other types if specified.
             * @function toObject
             * @memberof google.protobuf.Timestamp
             * @static
             * @param {google.protobuf.Timestamp} message Timestamp
             * @param {$protobuf.IConversionOptions} [options] Conversion options
             * @returns {Object.<string,*>} Plain object
             */
            Timestamp.toObject = function toObject(message, options) {
                if (!options)
                    options = {};
                var object = {};
                if (options.defaults) {
                    if ($util.Long) {
                        var long = new $util.Long(0, 0, false);
                        object.seconds = options.longs === String ? long.toString() : options.longs === Number ? long.toNumber() : long;
                    } else
                        object.seconds = options.longs === String ? "0" : 0;
                    object.nanos = 0;
                }
                if (message.seconds != null && message.hasOwnProperty("seconds"))
                    if (typeof message.seconds === "number")
                        object.seconds = options.longs === String ? String(message.seconds) : message.seconds;
                    else
                        object.seconds = options.longs === String ? $util.Long.prototype.toString.call(message.seconds) : options.longs === Number ? new $util.LongBits(message.seconds.low >>> 0, message.seconds.high >>> 0).toNumber() : message.seconds;
                if (message.nanos != null && message.hasOwnProperty("nanos"))
                    object.nanos = message.nanos;
                return object;
            };

            /**
             * Converts this Timestamp to JSON.
             * @function toJSON
             * @memberof google.protobuf.Timestamp
             * @instance
             * @returns {Object.<string,*>} JSON object
             */
            Timestamp.prototype.toJSON = function toJSON() {
                return this.constructor.toObject(this, $protobuf.util.toJSONOptions);
            };

            return Timestamp;
        })();

        return protobuf;
    })();

    return google;
})();

module.exports = $root;
