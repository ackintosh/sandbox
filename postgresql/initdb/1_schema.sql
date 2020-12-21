CREATE SCHEMA sandbox_schema;

-- https://www.postgresql.jp/document/12/html/tutorial-table.html
CREATE TABLE sandbox_schema.weather (
    city            varchar(80),

    temp_lo         int,           -- 最低気温
    temp_hi         int,           -- 最高気温
    prcp            real,          -- 降水量
    date            date
);
