var fs = require('fs');
var request = require('request');
var aws = require('aws-sdk');
var redis = require("redis");
var crypto = require('crypto');
var uuid = require('node-uuid');
var sizeOf = require('image-size');
var schedule = require('node-schedule');
var limit = require("simple-rate-limiter");
var propertiesReader = require('properties-reader');

// REQUIRE MULTIPLE INSTANCES OF PG-QUERY (EACH FOR EACH DIFFERENT ENVIRONMENT)
var query = require("pg-query");
delete require.cache[require.resolve("pg-query")];
var query2 = require("pg-query");
delete require.cache[require.resolve("pg-query")];
var query3 = require("pg-query");

var properties = propertiesReader('properties.file');

// FINAL VARIABLES
var MAX_PHOTOS = 3; // MAX PHOTOS PER CLUB
var MAX_QUERY_TRIES = 3; // MAX NUMBER OF RETRIES WHEN SERVER ERROR
var QUERY_RETRY_TIMEOUT = 2000; // WAIT 'QUERY_RETRY_TIMEOUT' SECONDS TO RETRY
var GOOGLE_PLACES_SEARCH_RADIUS = "20000"; // SEARCH PLACES WITHIN THIS DISTANCE (metres)
var GOOGLE_CLUBS_TYPES = ['restaurant', 'food', 'lodging', 'store', 'gym', 'school', 'park', 'amusement_park', 'movie_theater', 'hair_care', 'health', 'travel_agency'];
var FACEBOOK_PAGES_CATEGORIES = ['Bar', 'Club', 'Dance Club', 'Concert venue', 'Event venue', 'Bar & Grill', 'Dive Bar', 'Gay Bar', 'Inn', 'Jazz Club', 'Karaoke', 'Night Club', 'Party Center', 'Performance Venue', 'Pub', 'Wine Bar', 'Arts/entertainment/nightlife', 'Restaurant/cafe', 'Local business', 'Small business'];

// PROPERTIES
var AWS_ACCESS_KEY_ID = properties.get('aws.access.key');
var AWS_SECRET_ACCESS_KEY = properties.get('aws.secret.key');
var AWS_BUCKET_NAME_LOGS = properties.get('aws.s3.bucket.name.logs');
var AWS_BUCKET_NAME_IMAGES = properties.get('aws.s3.bucket.name.images');
var GOOGLE_API_KEY = properties.get('google.api.key');
var FACEBOOK_APP_ID = properties.get('facebook.app.id');
var FACEBOOK_ACCESS_TOKEN = properties.get('facebook.access.token');

// POSTGRESQL CONNECTION
query.connectionParameters = properties.get('aws.postgres.endpoint.development');
query2.connectionParameters = properties.get('aws.postgres.endpoint.stage');
query3.connectionParameters = properties.get('aws.postgres.endpoint.production');

//Set AWS configuration for future requests.
aws.config.update({"accessKeyId": AWS_ACCESS_KEY_ID, "secretAccessKey": AWS_SECRET_ACCESS_KEY, "region": "eu-west-1"});
aws.config.apiVersions = {
  dynamodb: '2012-08-10'
};

// API CALLS WITH RATE LIMITER IMPLEMENTED
var freeBaseAPI  = limit(function(first, second, third, callback) {
    var url = 'http://www.freebase.com/ajax/152a.lib.www.tags.svn.freebase-site.googlecode.dev/cuecard/mqlread.ajax?query={ "lang": "/lang/en", "query": [{ ' + first + ', ' + second + ', ' + third + ' }] }';
    request(url, callback);
}).to(8).per(1000);

var nightClubsAPI = limit(function(location, callback) {
    var url = "https://maps.googleapis.com/maps/api/place/nearbysearch/json?key=" + GOOGLE_API_KEY + "&location=" + location + "&radius=" + GOOGLE_PLACES_SEARCH_RADIUS  + "&types=night_club";
    request(url, callback);
}).to(1).per(1000);

var barAPI = limit(function(location, callback) {
    var url = "https://maps.googleapis.com/maps/api/place/nearbysearch/json?key=" + GOOGLE_API_KEY + "&location=" + location + "&radius=" + GOOGLE_PLACES_SEARCH_RADIUS  + "&types=bar";
    request(url, callback);
}).to(1).per(1000);

var additionalClubsAPI = limit(function(token, callback) {
    var url = "https://maps.googleapis.com/maps/api/place/nearbysearch/json?pagetoken=" + token + "&key=" + GOOGLE_API_KEY;
    request(url, callback);
}).to(1).per(1000);

var clubsDetailsAPI = limit(function(placeid, callback) {
    var url = "https://maps.googleapis.com/maps/api/place/details/json?placeid=" + placeid + "&key=" + GOOGLE_API_KEY;
    request(url, callback);
}).to(1).per(1000);

var clubsPicturesAPI  = limit(function(reference, callback) {
	var requestOptions  = { encoding: null, method: "GET", uri: "https://maps.googleapis.com/maps/api/place/photo?maxwidth=1600&photoreference=" + reference + "&sensor=false&key=" + GOOGLE_API_KEY};
    request(requestOptions, callback);
}).to(1).per(1000);

var facebookPageAPI = limit(function(query, callback) {
    var url = "https://graph.facebook.com/v2.2/search?access_token=" + FACEBOOK_APP_ID + "|" + FACEBOOK_ACCESS_TOKEN + "&format=json&method=get&pretty=0&q=" + query + "&suppress_http_code=1&type=page";
    request(url, callback);
}).to(1).per(1000);

var facebookPageDetailsAPI = limit(function(pageId, callback) {
    var url = "https://graph.facebook.com/v2.2/" + pageId + "?access_token=" + FACEBOOK_APP_ID + "|" + FACEBOOK_ACCESS_TOKEN + "&format=json&method=get&pretty=0&suppress_http_code=1";
    request(url, callback);
}).to(1).per(1000);

var facebookPictureAPI = limit(function(pageId, callback) {
    var requestOptions  = { encoding: null, method: "GET", uri: "https://graph.facebook.com/" + pageId + "/picture?width=1000"};
    request(requestOptions, callback);
}).to(1).per(1000);

// COUNTERS
var newClubs = 0;
var avoidedRepeatedCity = 0;
var avoidedRepeatedGoogleId = 0;

var getSecondLevelDivisionsInnerCounter = 0;
var getCitiesCounter = 0;
var getCitiesInnerCounter = 0;
var getCityCoordinatesCounter = 0;
var getBarsCounter = 0;
var getNightClubsCounter = 0;
var getAdditionalClubsCounter = 0;
var checkIfNewCounter = 0;
var facebookPageLookUpCounter = 0;
var getFacebookPageDetailsCounter = 0;
var checkIfNewFacebookIdCounter = 0;
var getClubDetailsCounter = 0;
var retrievePhotoFacebookCounter = 0;
var getPictureCounter = 0;
var saveClubCounter = 0;
var savePhotoCounter = 0;
var removePhotoCounter = 0;
var removePhotosCounter = 0;

// FLAGS
var hasReachedLimit = false;

// VARS & HOLDERS
var country = null;
var googleIds = [];
var facebookIds = [];
var freeBaseCitiesIds = [];
var cities = {};

var state = {
    cities : {
        total : 0,
        done : []
    },
    clubs : {
        done : []
    }
}

function initVars() {

	// GLOBAL VARIABLES
	newClubs = 0;
 	avoidedRepeatedCity = 0;
 	avoidedRepeatedGoogleId = 0;
 	getSecondLevelDivisionsInnerCounter = 0;
 	getCitiesCounter = 0;
 	getCitiesInnerCounter = 0;
 	getCityCoordinatesCounter = 0;
 	getBarsCounter = 0;
 	getNightClubsCounter = 0;
 	getAdditionalClubsCounter = 0;
 	checkIfNewCounter = 0;
 	facebookPageLookUpCounter = 0;
 	getFacebookPageDetailsCounter = 0;
 	checkIfNewFacebookIdCounter = 0;
 	getClubDetailsCounter = 0;
 	retrievePhotoFacebookCounter = 0;
 	getPictureCounter = 0;
 	saveClubCounter = 0;
 	savePhotoCounter = 0;
 	removePhotoCounter = 0;
 	removePhotosCounter = 0;

 	// FLAGS
	hasReachedLimit = false;

	// VARS & HOLDERS
	country = null;
	googleIds = [];
	facebookIds = [];
	freeBaseCitiesIds = [];
	cities = {};

	state = {
		cities : {
			total : 0,
			done : []
		},
		clubs : {
			done : []
		}
	}
}

// FUNCTIONS
function logDebug(message) {
	fs.appendFile('./logs/debug.txt', new Date().getTime() + ": " + message + "\n", function (err) {
		if (err) {
			throw err;
		}
	});
}

function logError(message) {
	fs.appendFile('./logs/errors.txt', new Date().getTime() + ": " + message + "\n", function (err) {
		if (err) {
			throw err;
		}
	});
}

function uploadLogs() {
	fs.exists('./logs/debug.txt', function (exists) {
		if (exists) {
			var today = new Date();
			var body = fs.readFileSync('./logs/debug.txt');
			var key = today.getUTCDate() + "-" + (today.getUTCMonth() + 1) + "-" + today.getUTCFullYear() + "_" + (("0" + today.getUTCHours()).slice(-2)) + ":" + (("0" + today.getUTCMinutes()).slice(-2)) + "_debug.txt";
			var s3 = new aws.S3({
				params : {
					Bucket : AWS_BUCKET_NAME_LOGS,
					Key : key
				}
			});
			
			s3.upload({Body : body}, function(err, data) {
				if (!err) {
					fs.unlinkSync('./logs/debug.txt');
				} else {
					logError("UPLOAD DEBUG LOGS TO S3 ERROR: " + err);
				}
			});
		}
	});
	
	
	fs.exists('./logs/errors.txt', function (exists) {
		if (exists) {
			var today = new Date();
			var body = fs.readFileSync('./logs/errors.txt');
			var key = today.getUTCDate() + "-" + (today.getUTCMonth() + 1) + "-" + today.getUTCFullYear() + "_" + (("0" + today.getUTCHours()).slice(-2)) + ":" + (("0" + today.getUTCMinutes()).slice(-2)) + "_errors.txt";
			var s3 = new aws.S3({
				params : {
					Bucket : AWS_BUCKET_NAME_LOGS,
					Key : key
				}
			});
			
			s3.upload({Body : body}, function(err, data) {
				if (!err) {
					fs.unlinkSync('./logs/errors.txt');
				} else {
					logError("UPLOAD ERRORS LOGS TO S3 ERROR: " + err);
				}
			});
		}
	});
}

// it does not work, does not remove objects for some reason *sigh*
function removePhotos(club) {
	var s3 = new aws.S3();
	var params = {
		Bucket : AWS_BUCKET_NAME_IMAGES,
		Delete: {
		    Objects: []
		}
	}

	club.picture_url.forEach(function(item) {
		params.Delete.Objects.push({Key: item.split("/").pop()});
	});

	s3.deleteObjects(params, function(err, data) {
		if (err) {
			logError("Deletion of club photos failed in S3: " + err);
		}
		removePhotosCounter--;
	});
}

// it does not work, does not remove objects for some reason *sigh*
function removePhoto(prefix) {
	var s3 = new aws.S3();
	var params = {
		Bucket : AWS_BUCKET_NAME_IMAGES,
		Key: prefix.split("/").pop()
	}

	s3.deleteObject(params, function(err, data) {
		if (err) {
			logError("Deletion of club photo failed in S3: " + err);
		}
		removePhotoCounter--;
	});
}

function savePhoto(club, uuid, prefix, isPrincipal) {
	var dynamodb = new aws.DynamoDB();
	var params = {
		TableName: "Clubs.Images",
	    Item: {
			"ClubId":{"S":uuid},
			"Prefix":{"S":prefix},
			"IsPrincipal":{"N":isPrincipal.toString()}
		}
	};

	dynamodb.putItem(params, function(err, data) {
		if (err) {
			logError("Save club image to dynamodb failed: " + err);
			removePhotoCounter++;
			removePhoto(prefix);
		}

		if (prefix == club.picture_url[club.picture_url.length - 1]) {
			newClubs++;
			if (state.clubs.done.indexOf(club.place_id) === -1) {
				state.clubs.done.push(club.place_id);
			}

			cities[club.freeBaseCity].done += 1;
			if (state.cities.done.indexOf(club.freeBaseCity) === -1 && cities[club.freeBaseCity].total === cities[club.freeBaseCity].done) {
				state.cities.done.push(club.freeBaseCity);
			}
		}
		savePhotoCounter--;
	});
}

function saveClub(club) {
	var createdAt = new Date().getTime();
	var id = uuid.v4();
	var profilePictureUrl = null;
	if (club.picture_url !== null) {
		profilePictureUrl = club.picture_url[0];
	}

	var item = {
		"Id":{"S":id},
		"GoogleId":{"S":club.googleId},
		"Name":{"S":club.name},
        "City":{"S":club.city},
        "Country":{"S":club.country},
        "Address":{"S":club.address},
    	"Offset":{"N":club.offset.toString()},
    	"UpdatedAt":{"N":createdAt.toString()},
    	"CreatedAt":{"N":createdAt.toString()}
	}

	if (profilePictureUrl != null) {
		item.ImagePrefix = {"S":profilePictureUrl};
	}
	if (club.facebookId != null) {
		item.FacebookId = {"S":club.facebookId};
	}
	if (club.description != null) {
		item.Description = {"S":club.description};
	}
	if (club.phone != null) {
		item.Phone = {"S":club.phone};
	}
	if (club.website != null) {
		item.Website = {"S":club.website};
	}

	var dynamodb = new aws.DynamoDB();
	var params = {
		TableName: "Clubs",
	    Item: item
	};

	dynamodb.putItem(params, function(err, data) {
		if (!err) {
			query("INSERT INTO clubs VALUES ($1, $2, ST_GeographyFromText('POINT(" + club.longitude + " " + club.latitude + ")'), DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT)", [id, club.name], function(err, rows, result) {
				if (!err) {
					query2("INSERT INTO clubs VALUES ($1, $2, ST_GeographyFromText('POINT(" + club.longitude + " " + club.latitude + ")'), DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT)", [id, club.name], function(err, rows, result) {
						if (!err) {
							query3("INSERT INTO clubs VALUES ($1, $2, ST_GeographyFromText('POINT(" + club.longitude + " " + club.latitude + ")'), DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT, DEFAULT)", [id, club.name], function(err, rows, result) {
								if (!err) {
									if (profilePictureUrl !== null) {
										var i = 0;
										club.picture_url.forEach(function(item) {
											savePhotoCounter++;
											if (i === 0) {
												savePhoto(club, id, item, 1);
											} else {
												savePhoto(club, id, item, 0);
											}
											i++;
										});
									} else {
										newClubs++;

										if (state.clubs.done.indexOf(club.place_id) === -1) {
											state.clubs.done.push(club.place_id);
										}

										cities[club.freeBaseCity].done += 1;
										if (state.cities.done.indexOf(club.freeBaseCity) === -1 && cities[club.freeBaseCity].total === cities[club.freeBaseCity].done) {
											state.cities.done.push(club.freeBaseCity);
										}
									}
									saveClubCounter--;
								} else {
									logError("Save club to PRODUCTION postgresql failed: " + err);
									query2("DELETE FROM clubs WHERE id=$1", [id], function(err, rows, result) {
										if(err) {
											logError("Deletion of club in stage postgresql failed: " + err);
										}
									});
									query("DELETE FROM clubs WHERE id=$1", [id], function(err, rows, result) {
										if(err) {
											logError("Deletion of club in development postgresql failed: " + err);
										}
									});
									dynamodb.deleteItem({
										"TableName": "Clubs",
				        				"Key": {"Id":{"S":id}}
				        			}, function(err, data) {
				        				if (err) {
				        					logError("Deletion of club in dynamodb failed: " + err);
				        				}
				        				saveClubCounter--;
									});
									if (profilePictureUrl !== null) {
										removePhotosCounter++;
										removePhotos(club);
									}

									if (state.clubs.done.indexOf(club.place_id) === -1) {
										state.clubs.done.push(club.place_id);
									}

									cities[club.freeBaseCity].done += 1;
									if (state.cities.done.indexOf(club.freeBaseCity) === -1 && cities[club.freeBaseCity].total === cities[club.freeBaseCity].done) {
										state.cities.done.push(club.freeBaseCity);
									}
								}
							});
						} else {
							logError("Save club to STAGE postgresql failed: " + err);
							query("DELETE FROM clubs WHERE id=$1", [id], function(err, rows, result) {
								if(err) {
									logError("Deletion of club in development postgresql failed: " + err);
								}
							});
							dynamodb.deleteItem({
								"TableName": "Clubs",
		        				"Key": {"Id":{"S":id}}
		        			}, function(err, data) {
		        				if (err) {
		        					logError("Deletion of club in dynamodb failed: " + err);
		        				}
		        				saveClubCounter--;
							});
							if (profilePictureUrl !== null) {
								removePhotosCounter++;
								removePhotos(club);
							}

							if (state.clubs.done.indexOf(club.place_id) === -1) {
								state.clubs.done.push(club.place_id);
							}

							cities[club.freeBaseCity].done += 1;
							if (state.cities.done.indexOf(club.freeBaseCity) === -1 && cities[club.freeBaseCity].total === cities[club.freeBaseCity].done) {
								state.cities.done.push(club.freeBaseCity);
							}
						}
					});
				} else {
					logError("Save club to DEVELOPMENT postgresql failed: " + err);
					dynamodb.deleteItem({
						"TableName": "Clubs",
        				"Key": {"Id":{"S":id}}
        			}, function(err, data) {
        				if (err) {
        					logError("Deletion of club in dynamodb failed: " + err);
        				}
        				saveClubCounter--;
					});
					if (profilePictureUrl !== null) {
						removePhotosCounter++;
						removePhotos(club);
					}

					if (state.clubs.done.indexOf(club.place_id) === -1) {
						state.clubs.done.push(club.place_id);
					}

					cities[club.freeBaseCity].done += 1;
					if (state.cities.done.indexOf(club.freeBaseCity) === -1 && cities[club.freeBaseCity].total === cities[club.freeBaseCity].done) {
						state.cities.done.push(club.freeBaseCity);
					}
				}
			});
		} else {
			logError("Save club to dynamodb failed: " + err);
			saveClubCounter--;

			if (state.clubs.done.indexOf(club.place_id) === -1) {
				state.clubs.done.push(club.place_id);
			}

			cities[club.freeBaseCity].done += 1;
			if (state.cities.done.indexOf(club.freeBaseCity) === -1 && cities[club.freeBaseCity].total === cities[club.freeBaseCity].done) {
				state.cities.done.push(club.freeBaseCity);
			}
		}
	});
}

function getPicture(googleResult, photoNumber, googlePhotoNumber, club, tryNumber) {
	if (!hasReachedLimit) {
		clubsPicturesAPI(googleResult.photos[googlePhotoNumber].photo_reference, function(error, response, body) {
			if (!error && response.statusCode === 200) {
				var format = response.headers['content-type'].split("/")[1];
				var shasum = crypto.createHash('sha1');
				shasum.update(club.googleId);
				var key = shasum.digest('hex').substring(0, 5) + '-' + new Date().getTime() + "-" + club.googleId + "." + format;
				
				var i = 0;
				var html_attributions = null;
				googleResult.photos[googlePhotoNumber].html_attributions.forEach(function(item) {
					if (i < googleResult.photos[googlePhotoNumber].html_attributions.length - 1) {
						html_attributions += item + " ";
						i++;
					} else {
						html_attributions += item;
					}
				});
				
				var metadata = {};
				metadata['x-amz-meta-offset_x'] = '0';
				metadata['x-amz-meta-offset_y'] = '0';
				metadata['x-amz-meta-height'] = googleResult.photos[googlePhotoNumber].height.toString();
				metadata['x-amz-meta-width'] = googleResult.photos[googlePhotoNumber].width.toString();
				if (html_attributions !== null) {
					metadata['x-amz-meta-html_attributions'] = html_attributions;
				}
				
				var s3 = new aws.S3({
					params : {
						Bucket : AWS_BUCKET_NAME_IMAGES,
						Key : key,
						Metadata : metadata
					}
				});
				
				s3.upload({Body : body}, function(err, data) {
					if (!err) {
						if (photoNumber === 1) {
							club.picture_url = [];
						}
						club.picture_url[club.picture_url.length] = "https://s3-eu-west-1.amazonaws.com/" + AWS_BUCKET_NAME_IMAGES + "/" + key;
						
						if (photoNumber === MAX_PHOTOS || googleResult.photos.length === googlePhotoNumber + 1) {
							saveClubCounter++;
							saveClub(club);
						} else {
							photoNumber++;
							retrievePhotoGoogle(googleResult, photoNumber, club);
						}
					} else {
						logError("getPicture, UPLOAD GOOGLE PICTURE TO S3 ERROR: " + err);
					}
					getPictureCounter--;
				});
			} else {
				if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
					tryNumber++;
					setTimeout(function() {
						getPicture(googleResult, photoNumber, googlePhotoNumber, club, tryNumber);
					}, QUERY_RETRY_TIMEOUT);
				} else {
					logError("getPicture, " + error + ", STATUS CODE: " + response.statusCode);
					getPictureCounter--;
				}
			}
		});
	} else {
		getPictureCounter--;
	}
}

function retrievePhotoGoogle(googleResult, photoNumber, club) {
	var googlePhotoNumber = photoNumber - 1;
	if (club.facebookId !== null) {
		googlePhotoNumber--;
	}
	getPictureCounter++;
	getPicture(googleResult, photoNumber, googlePhotoNumber, club, 1);
}

function retrievePhotoFacebook(googleResult, club, tryNumber) {
	facebookPictureAPI(club.facebookId, function(error, response, body) {
		if (!error && response.statusCode === 200) {
			var format = response.headers['content-type'].split("/")[1];
			var shasum = crypto.createHash('sha1');
			shasum.update(club.googleId);
			var key = shasum.digest('hex').substring(0, 5) + '-' + new Date().getTime() + "-" + club.googleId + "." + format;
			var dimensions = sizeOf(body);
			
			var metadata = {};
			metadata['x-amz-meta-offset_x'] = '0';
			metadata['x-amz-meta-offset_y'] = '0';
			metadata['x-amz-meta-height'] = dimensions.height.toString();
			metadata['x-amz-meta-width'] = dimensions.width.toString();
			
			var s3 = new aws.S3({
				params : {
					Bucket : AWS_BUCKET_NAME_IMAGES,
					Key : key,
					Metadata : metadata
				}
			});
			
			s3.upload({Body : body}, function(err, data) {
				if (!err) {
					club.picture_url = [];
					club.picture_url[club.picture_url.length] = "https://s3-eu-west-1.amazonaws.com/" + AWS_BUCKET_NAME_IMAGES + "/" + key;
					
					if (googleResult.hasOwnProperty("photos")) {
						retrievePhotoGoogle(googleResult, 2, club);
					} else {
						saveClubCounter++;
						saveClub(club);
					}
				} else {
					logError("UPLOAD FACEBOOK PICTURE TO S3 ERROR: " + err);
				}
				retrievePhotoFacebookCounter--;
			});
		} else {
			if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
				tryNumber++;
				setTimeout(function() {
					retrievePhotoFacebook(googleResult, club, tryNumber);
				}, QUERY_RETRY_TIMEOUT);
			} else {
				logError("retrievePhotoFacebook, " + error + ", STATUS CODE: " + response.statusCode);
				retrievePhotoFacebookCounter--;
			}
		}
	});
}

function retrievePhotos(googleResult, club) {
	if (club.facebookId !== null) {
		retrievePhotoFacebookCounter++;
		retrievePhotoFacebook(googleResult, club, 1);
	} else {
		retrievePhotoGoogle(googleResult, 1, club);
	}
}

function getClubDetails(club, description, facebookId, tryNumber) {
	if (!hasReachedLimit) {
		clubsDetailsAPI(club.place_id, function(error, response, body) {
			if (!error && response.statusCode === 200) {
				var json = JSON.parse(body.toString());
				if (json.status === 'OK'){
					var isCountry = true;
					json.result.address_components.forEach(function(item) {
						if (item.types.indexOf("country") > -1) {
							if (country !== item.long_name) {
								isCountry = false;
								return false;
							}
						}
					});
					
					if (!isCountry) {
						if (state.clubs.done.indexOf(club.place_id) === -1) {
							state.clubs.done.push(club.place_id);
						}

						cities[club.freeBaseCity].done += 1;
						if (state.cities.done.indexOf(club.freeBaseCity) === -1 && cities[club.freeBaseCity].total === cities[club.freeBaseCity].done) {
							state.cities.done.push(club.freeBaseCity);
						}

						getClubDetailsCounter--;
						return;
					}
					
					var city;
					json.result.address_components.forEach(function(item) {
						if (item.types.indexOf("locality") > -1 || item.types.indexOf("sublocality") > -1) {
							city = item.long_name;
						}
					});
					
					if (city === undefined || city.length < 1) {
						json.result.address_components.forEach(function(item) {
							if (item.types.indexOf("administrative_area_level_2") > -1) {
								city = item.long_name;
							}
						});
						
						if (city === undefined || city.length < 1) {
							json.result.address_components.forEach(function(item) {
								if (item.types.indexOf("administrative_area_level_1") > -1) {
									city = item.long_name;
								}
							});
							
							if (city === undefined || city.length < 1) {
								json.result.address_components.forEach(function(item) {
									if (item.types.indexOf("postal_town") > -1) {
										city = item.long_name;
									}
								});
							}
						}
					}
					
					if (city === undefined || city.length < 1) {
						logError("CITY UNDEFINED: " + JSON.stringify(json.result.address_components));

						if (state.clubs.done.indexOf(club.place_id) === -1) {
							state.clubs.done.push(club.place_id);
						}

						cities[club.freeBaseCity].done += 1;
						if (state.cities.done.indexOf(club.freeBaseCity) === -1 && cities[club.freeBaseCity].total === cities[club.freeBaseCity].done) {
							state.cities.done.push(club.freeBaseCity);
						}

						getClubDetailsCounter--;
						return;
					}
					
					var phone;
					if (json.result.hasOwnProperty("international_phone_number")) {
						phone = json.result.international_phone_number;
					} else if (json.result.hasOwnProperty("formatted_phone_number")) {
						phone = json.result.formatted_phone_number;
					} else{
						phone = null;
					}
					
					var website;
					if (json.result.hasOwnProperty("website")) {
						website = json.result.website;
					} else{
						website = null;
					}
					
					club.googleId = json.result.place_id;
					club.facebookId = facebookId;
					club.name = json.result.name;
					club.city = city;
					club.country = country;
					club.longitude = json.result.geometry.location.lng;
					club.latitude = json.result.geometry.location.lat;
					club.offset = json.result.utc_offset;
					club.address = json.result.formatted_address;
					club.description = description;
					club.website = website;
					club.phone = phone;
					
					if (json.result.hasOwnProperty("photos") || facebookId !== null) {
						retrievePhotos(json.result, club);
					} else {
						club.picture_url = null;
						saveClubCounter++;
						saveClub(club);
					}
				} else if (json.status === 'OVER_QUERY_LIMIT') {
					logDebug("getClubDetails, DAILY LIMIT REACHED");
					hasReachedLimit = true;
				}
				getClubDetailsCounter--;
			} else {
				if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
					tryNumber++;
					setTimeout(function() {
						getClubDetails(club, description, facebookId, tryNumber);
					}, QUERY_RETRY_TIMEOUT);
				} else {
					logError("getClubDetails, " + error + ", STATUS CODE: " + response.statusCode);
					getClubDetailsCounter--;
				}
			}
		});
	} else {
		getClubDetailsCounter--;
	}
}

function checkIfNewFacebookId(club, description, facebookId) {
	var dynamodb = new aws.DynamoDB();
	var params = {
		TableName: "Clubs",
	  	IndexName: "FacebookGlobalIndex",
	    KeyConditions: {
	    	"FacebookId": {
		      	ComparisonOperator: "EQ",
		      	AttributeValueList: [{"S" : facebookId}]
	    	}
	  	}
	};

	dynamodb.query(params, function(err, data) {
		if (!err) {
			getClubDetailsCounter++;
			if (data["Count"] === 0) {
				getClubDetails(club, description, facebookId, 1);
			} else {
				getClubDetails(club, null, null, 1);
			}
		} else {
			logError("COUNT QUERY BY FACEBOOK ID ERROR: " + err);

			if (state.clubs.done.indexOf(club.place_id) === -1) {
				state.clubs.done.push(club.place_id);
			}

			cities[club.freeBaseCity].done += 1;
			if (state.cities.done.indexOf(club.freeBaseCity) === -1 && cities[club.freeBaseCity].total === cities[club.freeBaseCity].done) {
				state.cities.done.push(club.freeBaseCity);
			}
		}
  		checkIfNewFacebookIdCounter--;
	});
}

function getFacebookPageDetails(facebookPages, index, club, tryNumber) {
	if (!hasReachedLimit) {
		facebookPageDetailsAPI(facebookPages.data[index].id, function(error, response, body) {
			if (!error && response.statusCode === 200) {
				var json = JSON.parse(body.toString());
				
				try {
					if (club.geometry.location.lat.toString().substring(0, 4) === json.location.latitude.toString().substring(0, 4) && club.geometry.location.lng.toString().substring(0, 4) === json.location.longitude.toString().substring(0, 4)) {
						var description;
						if (json.description !== undefined) {
							description = json.description.toString().split("\n")[0];
						} else {
							description = json.about.toString().split("\n")[0];
						}
						facebookIds[facebookIds.length] = facebookPages.data[index].id;
						checkIfNewFacebookIdCounter++;
						checkIfNewFacebookId(club, description, json.id);
					} else {
						if (index <= facebookPages.data.length) {
							index = index + 1;
							screenFacebookPageResults(facebookPages, index, club);
						} else {
							// NO FACEBOOK PAGE DETECTED FOR THIS CLUB
							getClubDetailsCounter++;
							getClubDetails(club, null, null, 1);
						}
					}
				} catch (ex) {
					if (index <= facebookPages.data.length) {
						index = index + 1;
						screenFacebookPageResults(facebookPages, index, club);
					} else {
						// NO FACEBOOK PAGE DETECTED FOR THIS CLUB
						getClubDetailsCounter++;
						getClubDetails(club, null, null, 1);
					}
				} finally {
					getFacebookPageDetailsCounter--;
				}
			} else {
				if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
					tryNumber++;
					setTimeout(function() {
						getFacebookPageDetails(facebookPages, index, club, tryNumber);
					}, QUERY_RETRY_TIMEOUT);
				} else {
					logError("getFacebookPageDetails, " + error + ", STATUS CODE: " + response.statusCode);
					getFacebookPageDetailsCounter--;
				}
			}
		});
	} else {
		getFacebookPageDetailsCounter--;
	}
}

function screenFacebookPageResults(facebookPages, index, club) {
	try {
		if (facebookIds.indexOf(facebookPages.data[index].id) > -1) {
			if (index <= facebookPages.data.length) {
				index = index + 1;
				screenFacebookPageResults(facebookPages, index, club);
			} else {
				// NO FACEBOOK PAGE DETECTED FOR THIS CLUB
				getClubDetailsCounter++;
				getClubDetails(club, null, null, 1);
			}
			return;
		}
	} catch (ex) {
		if (index <= facebookPages.data.length) {
			index = index + 1;
			screenFacebookPageResults(facebookPages, index, club);
		} else {
			// NO FACEBOOK PAGE DETECTED FOR THIS CLUB
			getClubDetailsCounter++;
			getClubDetails(club, null, null, 1);
		}
		return;
	}
	
	var category;
	try {
		category = facebookPages.data[index].category;
	} catch (ex) {
		if (index <= facebookPages.data.length) {
			index = index + 1;
			screenFacebookPageResults(facebookPages, index, club);
		} else {
			// NO FACEBOOK PAGE DETECTED FOR THIS CLUB
			getClubDetailsCounter++;
			getClubDetails(club, null, null, 1);
		}
		return;
	}
	
	if (FACEBOOK_PAGES_CATEGORIES.indexOf(category) > -1) {
		getFacebookPageDetailsCounter++;
		getFacebookPageDetails(facebookPages, index, club, 1);
	} else {
		if (index <= facebookPages.data.length) {
			index = index + 1;
			screenFacebookPageResults(facebookPages, index, club);
		} else {
			// NO FACEBOOK PAGE DETECTED FOR THIS CLUB
			getClubDetailsCounter++;
			getClubDetails(club, null, null, 1);
		}
	}
}

function facebookPageLookUp(club, tryNumber) {
	if (!hasReachedLimit) {
		facebookPageAPI(club.name, function(error, response, body) {
			if (!error && response.statusCode === 200) {
				var json = JSON.parse(body.toString());
				if (json.data !== null && json.data !== undefined && json.data.length !== 0) {
					screenFacebookPageResults(json, 0, club);
				} else {
					// NO FACEBOOK PAGE DETECTED FOR THIS CLUB
					getClubDetailsCounter++;
					getClubDetails(club, null, null, 1);
				}
				facebookPageLookUpCounter--;
			} else {
				if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
					tryNumber++;
					setTimeout(function() {
						facebookPageLookUp(club, tryNumber);
					}, QUERY_RETRY_TIMEOUT);
				} else {
					logError("facebookPageLookUp, " + error + ", STATUS CODE: " + response.statusCode);
					
					// FACEBOOK DOES NOT RESPOND, CONTINUE WITHOUT FACEBOOK PAGE SEARCH
					getClubDetailsCounter++;
					getClubDetails(club, null, null, 1);

					facebookPageLookUpCounter--;
				}
			}
		});
	} else {
		facebookPageLookUpCounter--;
	}
}

function checkIfNew(club) {
	var dynamodb = new aws.DynamoDB();
	var params = {
		TableName: "Clubs",
	  	IndexName: "GoogleGlobalIndex",
	    KeyConditions: {
	    	"GoogleId": {
		      	ComparisonOperator: "EQ",
		      	AttributeValueList: [{"S" : club.place_id}]
	    	}
	  	}
	};

	dynamodb.query(params, function(err, data) {
		if (!err) {
			if (data["Count"] === 0) {
				facebookPageLookUpCounter++;
				facebookPageLookUp(club, 1);
			} else {
				avoidedRepeatedGoogleId++;

				if (state.clubs.done.indexOf(club.place_id) === -1) {
					state.clubs.done.push(club.place_id);
				}

				cities[club.freeBaseCity].done += 1;
				if (state.cities.done.indexOf(club.freeBaseCity) === -1 && cities[club.freeBaseCity].total ===cities[club.freeBaseCity].done) {
					state.cities.done.push(club.freeBaseCity);
				}
			}
		} else {
			logError("Check if new google id in dynamodb failed: " + err);

			if (state.clubs.done.indexOf(club.place_id) === -1) {
				state.clubs.done.push(club.place_id);
			}

			cities[club.freeBaseCity].done += 1;
			if (state.cities.done.indexOf(club.freeBaseCity) === -1 && cities[club.freeBaseCity].total === cities[club.freeBaseCity].done) {
				state.cities.done.push(club.freeBaseCity);
			}
		}
  		checkIfNewCounter--;
	});
}

function checkIfValid(club) {
	var isValid = true;
	club.types.forEach(function(item) {
		if (GOOGLE_CLUBS_TYPES.indexOf(item) > -1) {
			isValid = false;
		}
	});
	
	if (isValid) {
		checkIfNewCounter++;
		checkIfNew(club);
	} else {
		if (state.clubs.done.indexOf(club.place_id) === -1) {
			state.clubs.done.push(club.place_id);
		}
			
		cities[club.freeBaseCity].done += 1;
		if (state.cities.done.indexOf(club.freeBaseCity) === -1 && cities[club.freeBaseCity].total === cities[club.freeBaseCity].done) {
			state.cities.done.push(club.freeBaseCity);
		}
	}
}

function getAdditionalClubs(nextPageToken, isNightClub, tryNumber, freeBaseCity) {
	if (!hasReachedLimit) {
		additionalClubsAPI(nextPageToken, function(error, response, body) {
			if (!error && response.statusCode === 200) {
				var json = JSON.parse(body.toString());
				if (json.status === 'OK'){
					processClubs(json, isNightClub, freeBaseCity);
					getAdditionalClubsCounter--;
				} else if (json.status === 'INVALID_REQUEST') {
					// RETRY (NEXT PAGE TOKEN MIGHT HAVE NOT BEEN READY YET)
					setTimeout(function() {
						additionalClubsAPI(nextPageToken, function(error, response, body) {
							if (!error && response.statusCode === 200) {
								var json = JSON.parse(body.toString());
								if (json.status === 'OK') {
									processClubs(json, isNightClub, freeBaseCity);
								} else if (json.status === 'OVER_QUERY_LIMIT') {
									logDebug("getAdditionalClubs, DAILY LIMIT REACHED");
									hasReachedLimit = true;
								}
								getAdditionalClubsCounter--;
							}else{
								if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
									tryNumber++;
									setTimeout(function() {
										getAdditionalClubs(nextPageToken, isNightClub, tryNumber, freeBaseCity);
									}, QUERY_RETRY_TIMEOUT);
								} else {
									logError("getAdditionalClubs, " + error + ", STATUS CODE: " + response.statusCode);
									getAdditionalClubsCounter--;
								}
							}
						});
					}, QUERY_RETRY_TIMEOUT);
				} else if (json.status === 'OVER_QUERY_LIMIT') {
					logDebug("getAdditionalClubs, DAILY LIMIT REACHED");
					hasReachedLimit = true;
					getAdditionalClubsCounter--;
				}
			} else {
				if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
					tryNumber++;
					setTimeout(function() {
						getAdditionalClubs(nextPageToken, isNightClub, tryNumber, freeBaseCity);
					}, QUERY_RETRY_TIMEOUT);
				} else {
					logError("getAdditionalClubs2, " + error + ", STATUS CODE: " + response.statusCode);
					getAdditionalClubsCounter--;
				}
			}
		});
	} else {
		getAdditionalClubsCounter--;
	}
}

function processClubs(clubs, isNightClub, freeBaseCity) {
	cities[freeBaseCity].total += clubs.results.length;
	for (var i = 0; i < clubs.results.length; i++) {
		try {
			if (state.clubs.done.indexOf(clubs.results[i].id) === -1 && googleIds.indexOf(clubs.results[i].id) === -1) {
				googleIds[googleIds.length] = clubs.results[i].id;
				var club = clubs.results[i];
				club.freeBaseCity = freeBaseCity;
				if (isNightClub) {
					checkIfNewCounter++;
					checkIfNew(club);
				} else {
					checkIfValid(club);
				}
			} else {
				if (googleIds.indexOf(clubs.results[i].id) === -1) {
					googleIds.push(clubs.results[i].id);
				}

				cities[freeBaseCity].done += 1;
				if (state.cities.done.indexOf(freeBaseCity) === -1 && cities[freeBaseCity].total === cities[freeBaseCity].done) {
					state.cities.done.push(freeBaseCity);
				}
			}	
		} catch (ex) {
			logError("NO GOOGLE ID...: " + clubs.results[i]);
			cities[freeBaseCity].done += 1;
			if (state.cities.done.indexOf(freeBaseCity) === -1 && cities[freeBaseCity].total === cities[freeBaseCity].done) {
				state.cities.done.push(freeBaseCity);
			}
		}
	}
	
	if (clubs.next_page_token !== undefined) {
		getAdditionalClubsCounter++;
		getAdditionalClubs(clubs.next_page_token, isNightClub, 1, freeBaseCity);
	} else {
		cities[freeBaseCity].queries++;
		if (cities[freeBaseCity].queries === 2 && 
			state.cities.done.indexOf(freeBaseCity) === -1 && 
			cities[freeBaseCity].total === cities[freeBaseCity].done) {

			state.cities.done.push(freeBaseCity);
		}
	}
}

function getNightClubs(location, tryNumber, freeBaseCity) {
	if (!hasReachedLimit) {
		nightClubsAPI(location, function(error, response, body) {
			if (!error && response.statusCode === 200) {
				var json = JSON.parse(body.toString());
				if (json.status === 'OK' || json.status === 'ZERO_RESULTS'){
					processClubs(json, true, freeBaseCity);
				} else if (json.status === 'OVER_QUERY_LIMIT') {
					logDebug("getNightClubs, DAILY LIMIT REACHED");
					hasReachedLimit = true;
				} else {
					logError("STATUS GETCLUBS:" + json.status);
				}
				getNightClubsCounter--;
			} else {
				if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
					tryNumber++;
					setTimeout(function() {
						getNightClubs(location, tryNumber, freeBaseCity);
					}, QUERY_RETRY_TIMEOUT);
				} else {
					logError("getNightClubs, " + error + ", STATUS CODE: " + response.statusCode);
					getNightClubsCounter--;
				}
			}
		});
	} else {
		getNightClubsCounter--;
	}
}

function getBars(location, tryNumber, freeBaseCity) {
	if (!hasReachedLimit) {
		barAPI(location, function(error, response, body) {
			if (!error && response.statusCode === 200) {
				var json = JSON.parse(body.toString());
				if (json.status === 'OK' || json.status === 'ZERO_RESULTS') {
					processClubs(json, false, freeBaseCity);
				} else if (json.status === 'OVER_QUERY_LIMIT') {
					logDebug("getBars, DAILY LIMIT REACHED");
					hasReachedLimit = true;
				} else {
					logError("STATUS GETCLUBS:" + json.status);
				}
				getBarsCounter--;
			} else {
				if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
					tryNumber++;
					setTimeout(function() {
						getBars(location, tryNumber, freeBaseCity);
					}, QUERY_RETRY_TIMEOUT);
				} else {
					logError("getBars, " + error + ", STATUS CODE: " + response.statusCode);
					getBarsCounter--;
				}
			}
		});
	} else {
		getBarsCounter--;
	}
}

function getCityCoordinates(id, name, isNewCountry, tryNumber) {
	if (!hasReachedLimit) {
		freeBaseAPI('"id": "' + id + '"', '"type": "/location/location"', '"geolocation": [{ "latitude": null, "longitude": null }]', function(error, response, body) {
			if (!error && response.statusCode === 200) {
				hasStartedCityCounter = true;
				var json = JSON.parse(body.toString());
				if (json.status === "200 OK") {
					if (json.result.result.length > 0 && cities[name] === undefined) {
						if (isNewCountry) {
							state.cities.total++;
						}

						if (isNewCountry || state.cities.done.indexOf(name) === -1) {
							cities[name] = {"total" : 0, "done": 0, "queries": 0};
							var latitude = json.result.result[0].geolocation[0].latitude;
							var longitude = json.result.result[0].geolocation[0].longitude;
							var location = latitude + "," + longitude;
							getNightClubsCounter++;
							getBarsCounter++;
							getNightClubs(location, 1, name);
							getBars(location, 1, name);
						}
					}
					getCityCoordinatesCounter--;
				}else{
					if (json.error.code === 503 && tryNumber <= MAX_QUERY_TRIES) {
						tryNumber++;
						setTimeout(function() {
							getCityCoordinates(id, name, isNewCountry, tryNumber);
						}, QUERY_RETRY_TIMEOUT);
					} else {
						logError("getCityCoordinates, ERROR: " + json.status + ". JSON: " + JSON.stringify(json) + ", NAME: " + name);
						getCityCoordinatesCounter--;
					}
				}
			} else {
				if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
					tryNumber++;
					setTimeout(function() {
						getCityCoordinates(id, name, isNewCountry, tryNumber);
					}, QUERY_RETRY_TIMEOUT);
				} else {
					logError("getCityCoordinates2, " + error + ", STATUS CODE: " + response.statusCode + ", NAME: " + name);
					getCityCoordinatesCounter--;
				}
			}
		});
	} else {
		getCityCoordinatesCounter--;
	}
}

function getCitiesInner(name, isNewCountry, tryNumber) {
	if (!hasReachedLimit) {
		freeBaseAPI('"id": null', '"name": "' + name + '"', '"type": "/location/location"', function(error, response, body) {
			if (!error && response.statusCode === 200) {
				var json = JSON.parse(body.toString());
				if (json.status === "200 OK") {
					getCitiesCounter++;
					getCities(json.result.result[0].id, isNewCountry, 1);
					getCitiesInnerCounter--;
				}else{
					if (json.error.code === 503 && tryNumber <= MAX_QUERY_TRIES) {
						tryNumber++;
						setTimeout(function() {
							getCitiesInner(name, isNewCountry, tryNumber);
						}, QUERY_RETRY_TIMEOUT);
					} else {
						logError("getCitiesInner, ERROR: " + json.status + ". JSON: " + JSON.stringify(json) + ", NAME: " + name);
						getCitiesInnerCounter--;
					}
				}
			} else {
				if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
					tryNumber++;
					setTimeout(function() {
						getCitiesInner(name, isNewCountry, tryNumber);
					}, QUERY_RETRY_TIMEOUT);
				} else {
					logError("getCitiesInner2, " + error + ", STATUS CODE: " + response.statusCode + ", NAME: " + name);
					getCitiesInnerCounter--;
				}
			}
		});
	} else {
		getCitiesInnerCounter--;
	}
}

function getCities(id, isNewCountry, tryNumber) {
	if (!hasReachedLimit && freeBaseCitiesIds.indexOf(id) === -1) {
		freeBaseCitiesIds[freeBaseCitiesIds.length] = id;
		freeBaseAPI('"id": "' + id + '"', '"name": null', '"/location/location/contains": []', function(error, response, body) {
			if (!error && response.statusCode === 200) {
				var json = JSON.parse(body.toString());
				if (json.status === "200 OK") {
					if (json.result.result[0]["/location/location/contains"].length > 0){
						json.result.result[0]["/location/location/contains"].forEach(function(item) {
							// CHECK FOR INVALID CHARACTERS
							if (item !== null && item !== undefined && item.indexOf('&') === -1 && item.indexOf('"') === -1) {
								getCitiesInnerCounter++;
								getCitiesInner(item, isNewCountry, 1);
							}
						});
					} else {
						getCityCoordinatesCounter++;
						getCityCoordinates(id, json.result.result[0].name, isNewCountry, 1);
					}
					getCitiesCounter--;
				}else{
					if (json.error.code === 503 && tryNumber <= MAX_QUERY_TRIES) {
						tryNumber++;
						setTimeout(function() {
							getCities(id, isNewCountry, tryNumber);
						}, QUERY_RETRY_TIMEOUT);
					} else {
						logError("getCities, ERROR: " + json.status + ". JSON: " + JSON.stringify(json) + ", ID: " + id);
						getCitiesCounter--;
					}
				}
			} else {
				if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
					tryNumber++;
					setTimeout(function() {
						getCities(id, isNewCountry, tryNumber);
					}, QUERY_RETRY_TIMEOUT);
				} else {
					logError("getCities2, " + error + ", STATUS CODE: " + response.statusCode + ", ID: " + id);
					getCitiesCounter--;
				}
			}
		});
	} else {
		getCitiesCounter--;
		avoidedRepeatedCity++;
	}
}

function getSecondLevelDivisionsInner(name, isNewCountry, tryNumber) {
	hasStarted = true;
	if (!hasReachedLimit) {
		freeBaseAPI('"id": null', '"name": "' + name + '"', '"type": "/location/administrative_division"', function(error, response, body) {
			if (!error && response.statusCode === 200) {
				var json = JSON.parse(body.toString());
				if (json.status === "200 OK") {
					getCitiesCounter++;
					getCities(json.result.result[0].id, isNewCountry, 1);
					getSecondLevelDivisionsInnerCounter--;
				}else{
					if (json.error.code === 503 && tryNumber <= MAX_QUERY_TRIES) {
						tryNumber++;
						setTimeout(function() {
							getSecondLevelDivisionsInner(name, isNewCountry, tryNumber);
						}, QUERY_RETRY_TIMEOUT);
					} else {
						logError("getSecondLevelDivisionsInner, ERROR: " + json.status + ". JSON: " + JSON.stringify(json) + ", NAME: " + name);
						getSecondLevelDivisionsInnerCounter--;
					}
				}
			} else {
				if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
					tryNumber++;
					setTimeout(function() {
						getSecondLevelDivisionsInner(name, isNewCountry, tryNumber);
					}, QUERY_RETRY_TIMEOUT);
				} else {
					logError("getSecondLevelDivisionsInner2, " + error + ", STATUS CODE: " + response.statusCode + ", NAME: " + name);
					getSecondLevelDivisionsInnerCounter--;
				}
			}
		});
	} else {
		getSecondLevelDivisionsInnerCounter--;
	}
}

function getSecondLevelDivisions(id, isNewCountry, tryNumber) {
	if (!hasReachedLimit) {
		freeBaseAPI('"id": "' + id + '"', '"name": null', '"/location/country/second_level_divisions": []', function(error, response, body) {
			if (!error && response.statusCode === 200) {
				var json = JSON.parse(body.toString());
				if (json.status === "200 OK") {
					json.result.result[0]["/location/country/second_level_divisions"].forEach(function(item) {
						getSecondLevelDivisionsInnerCounter++;
						getSecondLevelDivisionsInner(item, isNewCountry, 1);
					});
				} else {
					if (json.error.code === 503 && tryNumber <= MAX_QUERY_TRIES) {
						tryNumber++;
						setTimeout(function() {
							getSecondLevelDivisions(id, isNewCountry, tryNumber);
						}, QUERY_RETRY_TIMEOUT);
					} else {
						logError("getSecondLevelDivisions, ERROR: " + json.status + ". JSON: " + JSON.stringify(json) + ", ID: " + id);
					}
				}
			} else {
				if (response.statusCode === 500 && tryNumber <= MAX_QUERY_TRIES) {
					tryNumber++;
					setTimeout(function() {
						getSecondLevelDivisions(id, isNewCountry, tryNumber);
					}, QUERY_RETRY_TIMEOUT);
				} else {
					logError("getSecondLevelDivisions2, " + error + ", STATUS CODE: " + response.statusCode + ", ID: " + id);
					hasStarted = true;
				}
			}
		});
	}
}

function getCountry(isNewCountry) {
	freeBaseAPI('"id": null', '"name": null', '"type": "/location/country"', function(error, response, body) {
		if (!error && response.statusCode === 200) {
			var json = JSON.parse(body.toString());
			if (json.status === "200 OK") {
				json.result.result.forEach(function(item) {
					if(item.name === country) {
						getSecondLevelDivisions(item.id, isNewCountry, 1);
						return false;
					}
				});
			} else {
				logError("countries, ERROR: " + json.status + ". JSON: " + JSON.stringify(json));
				hasStarted = true;
			}
		} else {
			logError("countries2. " + error);
			hasStarted = true;
		}
	});
}

function areFunctionsDone() {
    if (getSecondLevelDivisionsInnerCounter === 0 &&
            getCitiesCounter === 0 &&
            getCitiesInnerCounter === 0 &&
            getCityCoordinatesCounter === 0 &&
            getBarsCounter === 0 &&
            getNightClubsCounter === 0 &&
            getAdditionalClubsCounter === 0 &&
            checkIfNewCounter === 0 &&
            facebookPageLookUpCounter === 0 &&
            getFacebookPageDetailsCounter === 0 &&
            checkIfNewFacebookIdCounter === 0 &&
            getClubDetailsCounter === 0 &&
            retrievePhotoFacebookCounter === 0 &&
            getPictureCounter === 0 &&
            saveClubCounter === 0 &&
            savePhotoCounter === 0 &&
            removePhotoCounter === 0 &&
            removePhotosCounter === 0) {
        return true;
    } else {
        return false;
    }
}

// MAIN EXECUTION
redisClient = redis.createClient();
var j = schedule.scheduleJob('0 * * * *', function() {
    redisClient.get("running", function (err, reply) {
	    if ("false" === reply.toString()) {
			initVars();
			redisClient.get("countries", function (err, reply) {
				if (reply != null) {
					var countries = JSON.parse(reply.toString());
					if (countries.length > 0) {
						redisClient.set("running", true);
						country = countries[0];

						redisClient.get("state", function (err, reply) {
							var isNewCountry;
							if (reply != null) {
								state = JSON.parse(reply.toString());
								isNewCountry = false;
							} else {
								isNewCountry = true;
							}
							hasStarted = false;
							hasStartedCityCounter = false;
							previousStateCitiesTotal = -1;
							previousProgress = -1;
							getCountry(isNewCountry);

							var interval2 = setInterval(function() {
								if (hasStartedCityCounter) {
									if (state.cities.total === previousStateCitiesTotal) {
										var progress = state.cities.done.length;
										if (progress !== previousProgress) {
											previousProgress = progress;
											logDebug(progress + "/" + state.cities.total + " finished");
										}
									} else {
										previousStateCitiesTotal = state.cities.total;
									}
								}
							}, 10000);

							var interval = setInterval(function() {
								if (areFunctionsDone() && hasStarted) {
									clearInterval(interval);
									clearInterval(interval2);

									uploadLogs();
									if (!hasReachedLimit) {
										redisClient.del("state");

										countries.shift();
										if (countries.length === 0) {
											redisClient.del("countries");
										} else {
											redisClient.set("countries", JSON.stringify(countries));
										}
									} else {
										redisClient.set("state", JSON.stringify(state));
									}
									redisClient.set("running", false);
								}
							}, 5000);
						});
					}	
				}	
			});
		}
	});
});